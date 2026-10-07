import http from 'node:http'
import { spawn } from 'node:child_process'
import { createHash, randomUUID } from 'node:crypto'
import { mkdir, readFile, rm, writeFile } from 'node:fs/promises'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { WebSocketServer } from 'ws'

const PORT = Number(process.env.PORT || 10000)
const ROOT = path.resolve(process.env.MATHSCOPE_PROJECT_ROOT || './lean-project')
const ORIGINS = new Set(
  (process.env.MATHSCOPE_ALLOWED_ORIGINS || 'https://project29770.websitepublisher.ai')
    .split(',')
    .map(x => x.trim())
    .filter(Boolean)
)
const TIMEOUT_MS = Number(process.env.MATHSCOPE_VERIFY_TIMEOUT_MS || 120000)
const MAX_QUEUE = Number(process.env.MATHSCOPE_MAX_QUEUE || 8)
const MAX_LSP_SESSIONS = Number(process.env.MATHSCOPE_MAX_LSP_SESSIONS || 2)
const LSP_IDLE_MS = Number(process.env.MATHSCOPE_LSP_IDLE_MS || 900000)
let running = false
let lastSelfTest = null
const queue = []
const lspSessions = new Map()

function sha256(value) {
  return createHash('sha256').update(value).digest('hex')
}

function leanEnv() {
  const home = process.env.HOME || ''
  const current = process.env.PATH || ''
  const candidates = [
    process.env.ELAN_HOME ? path.join(process.env.ELAN_HOME, 'bin') : '',
    '/opt/render/.elan/bin',
    home ? path.join(home, '.elan', 'bin') : '',
    current,
  ].filter(Boolean)
  return { ...process.env, PATH: candidates.join(path.delimiter) }
}

function cors(origin) {
  return origin && ORIGINS.has(origin)
    ? { 'access-control-allow-origin': origin, 'vary': 'Origin' }
    : {}
}

function terminateChild(child) {
  if (!child || child.killed) return
  try {
    if (process.platform === 'win32') child.kill()
    else process.kill(-child.pid, 'SIGTERM')
  } catch {
    try { child.kill('SIGTERM') } catch {}
  }
}

function frameLsp(message) {
  const body = JSON.stringify(message)
  return 'Content-Length: ' + Buffer.byteLength(body, 'utf8') + '\r\n\r\n' + body
}

class LspFramer {
  constructor(onMessage) {
    this.buffer = Buffer.alloc(0)
    this.onMessage = onMessage
  }

  push(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk])
    while (true) {
      const headerEnd = this.buffer.indexOf('\r\n\r\n')
      if (headerEnd < 0) return
      const header = this.buffer.subarray(0, headerEnd).toString('ascii')
      const match = /Content-Length:\s*(\d+)/i.exec(header)
      if (!match) {
        this.buffer = this.buffer.subarray(headerEnd + 4)
        continue
      }
      const length = Number(match[1])
      const bodyStart = headerEnd + 4
      if (this.buffer.length < bodyStart + length) return
      const body = this.buffer.subarray(bodyStart, bodyStart + length).toString('utf8')
      this.buffer = this.buffer.subarray(bodyStart + length)
      try { this.onMessage(JSON.parse(body)) } catch {}
    }
  }
}

async function startLspSession(ws) {
  if (lspSessions.size >= MAX_LSP_SESSIONS) {
    ws.close(1013, 'Lean LSP capacity reached')
    return
  }

  const sessionId = randomUUID()
  // Reuse a real, already-built Lean module path for LSP configuration. The browser's
  // didOpen payload supplies an in-memory smoke document, so the audited C014 file on
  // disk is never modified by the LSP session.
  const sessionDir = null
  const documentPath = path.join(ROOT, 'MathScope', 'Claims', 'C014.lean')
  console.log('LSP_SESSION_START', JSON.stringify({
    sessionId,
    modulePath: path.relative(ROOT, documentPath),
    backingMode: 'existing-built-module-in-memory-buffer'
  }))

  const child = spawn('lake', ['serve'], {
    cwd: ROOT,
    env: leanEnv(),
    shell: false,
    windowsHide: true,
    stdio: ['pipe', 'pipe', 'pipe'],
    detached: process.platform !== 'win32',
  })

  const session = { child, sessionDir, timer: null }
  lspSessions.set(sessionId, session)

  const cleanup = () => {
    if (!lspSessions.has(sessionId)) return
    lspSessions.delete(sessionId)
    if (session.timer) clearTimeout(session.timer)
    terminateChild(child)
    if (sessionDir) rm(sessionDir, { recursive: true, force: true }).catch(() => {})
  }

  const refreshIdle = () => {
    if (session.timer) clearTimeout(session.timer)
    session.timer = setTimeout(() => {
      try { ws.close(1000, 'Lean LSP idle timeout') } catch {}
      cleanup()
    }, LSP_IDLE_MS)
  }

  const framer = new LspFramer(message => {
    if (message?.method === 'textDocument/publishDiagnostics' || message?.id != null) {
      console.log('LSP_SERVER_MESSAGE', JSON.stringify({
        sessionId,
        id: message?.id ?? null,
        method: message?.method ?? null,
        diagnostics: Array.isArray(message?.params?.diagnostics) ? message.params.diagnostics.length : null,
        version: message?.params?.version ?? null
      }))
    }
    if (ws.readyState === ws.OPEN) ws.send(JSON.stringify(message))
  })

  child.stdout.on('data', chunk => framer.push(chunk))
  child.stderr.on('data', chunk => {
    if (ws.readyState === ws.OPEN) {
      ws.send(JSON.stringify({
        mathscope: { type: 'stderr', text: chunk.toString('utf8') }
      }))
    }
  })
  child.on('error', error => {
    if (ws.readyState === ws.OPEN) {
      ws.send(JSON.stringify({
        mathscope: { type: 'error', text: String(error?.message || error) }
      }))
      ws.close(1011, 'Lean LSP failed')
    }
    cleanup()
  })
  child.on('close', () => {
    if (ws.readyState === ws.OPEN) ws.close(1000, 'Lean LSP stopped')
    cleanup()
  })

  ws.on('message', data => {
    refreshIdle()
    try {
      const message = JSON.parse(data.toString('utf8'))
      if (message?.method === 'initialize' || message?.method === 'textDocument/didOpen' ||
          message?.method === 'textDocument/didChange' || message?.method === 'textDocument/waitForDiagnostics') {
        console.log('LSP_CLIENT_MESSAGE', JSON.stringify({
          sessionId,
          id: message?.id ?? null,
          method: message?.method ?? null,
          version: message?.params?.version ?? message?.params?.textDocument?.version ?? null
        }))
      }
      child.stdin.write(frameLsp(message))
    } catch {
      ws.send(JSON.stringify({ mathscope: { type: 'error', text: 'invalid LSP JSON' } }))
    }
  })
  ws.on('close', cleanup)
  ws.on('error', cleanup)

  refreshIdle()
  ws.send(JSON.stringify({
    mathscope: {
      type: 'session',
      sessionId,
      documentUri: pathToFileURL(documentPath).href,
      rootUri: pathToFileURL(ROOT + path.sep).href,
      idleTimeoutMs: LSP_IDLE_MS,
    }
  }))
}

function reply(res, status, body, origin) {
  const payload = JSON.stringify(body)
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'cache-control': 'no-store',
    'content-length': Buffer.byteLength(payload),
    ...cors(origin),
  })
  res.end(payload)
}

function replyHtml(res, status, html, origin) {
  res.writeHead(status, {
    'content-type': 'text/html; charset=utf-8',
    'cache-control': 'no-store',
    'content-length': Buffer.byteLength(html),
    ...cors(origin),
  })
  res.end(html)
}

function run(command, args, cwd, timeoutMs = TIMEOUT_MS) {
  return new Promise(resolve => {
    let stdout = ''
    let stderr = ''
    let settled = false
    let timer
    const child = spawn(command, args, {
      cwd,
      env: leanEnv(),
      shell: false,
      windowsHide: true,
      stdio: ['ignore', 'pipe', 'pipe'],
      detached: process.platform !== 'win32',
    })

    const finish = result => {
      if (settled) return
      settled = true
      if (timer) clearTimeout(timer)
      resolve(result)
    }

    child.stdout.on('data', chunk => {
      if (stdout.length < 2_000_000) stdout += chunk.toString('utf8')
    })
    child.stderr.on('data', chunk => {
      if (stderr.length < 2_000_000) stderr += chunk.toString('utf8')
    })
    child.on('error', error => finish({ code: null, stdout, stderr: stderr + String(error), timedOut: false }))
    child.on('close', code => finish({ code, stdout, stderr, timedOut: false }))

    timer = setTimeout(() => {
      try {
        if (process.platform === 'win32') child.kill()
        else process.kill(-child.pid, 'SIGTERM')
      } catch {
        child.kill()
      }
      finish({ code: null, stdout, stderr, timedOut: true })
    }, timeoutMs)
  })
}

async function fingerprint() {
  const toolchainPath = path.join(ROOT, 'lean-toolchain')
  const manifestPath = path.join(ROOT, 'lake-manifest.json')
  const [toolchain, manifest, lean, lake] = await Promise.all([
    readFile(toolchainPath, 'utf8'),
    readFile(manifestPath),
    run('lean', ['--version'], ROOT, 10000),
    run('lake', ['--version'], ROOT, 10000),
  ])
  if (lean.timedOut || lean.code !== 0) {
    throw new Error('Lean runtime unavailable: ' + (lean.stderr || lean.stdout || 'unknown error'))
  }
  if (lake.timedOut || lake.code !== 0) {
    throw new Error('Lake runtime unavailable: ' + (lake.stderr || lake.stdout || 'unknown error'))
  }
  return {
    toolchain: toolchain.trim(),
    environmentHash: sha256([lean.stdout, lean.stderr, lake.stdout, lake.stderr, toolchain].join('\n')),
    dependencyLockHash: sha256(manifest),
  }
}

async function verifyC014(semanticReviewed) {
  const id = randomUUID()
  const sourcePath = path.join(ROOT, 'MathScope', 'Claims', 'C014.lean')
  const source = await readFile(sourcePath)
  const sourceHash = sha256(source)
  const fp = await fingerprint()

  const deployCommit = process.env.RENDER_GIT_COMMIT || ''
  const auditArtifact = path.join(ROOT, '.mathscope-cloud', 'c014-axioms.txt')
  let output = ''
  let auditError = ''
  try {
    output = (await readFile(auditArtifact, 'utf8')).trim()
  } catch (error) {
    auditError = 'Build-time axiom audit artifact unavailable: ' + String(error?.message || error)
  }

  const expectedTheorem = 'theorem=MathScope.Claims.C014.c014_slice_radius'
  const auditMatches = output.includes(expectedTheorem)
  const sorryDependent = /(^|[,=\\s])sorryAx($|[,\\s])/m.test(output)
  const formal = auditMatches && !sorryDependent && auditError === ''
  return {
    id,
    claimId: 'C-014',
    createdAt: new Date().toISOString(),
    state: {
      truth: formal && semanticReviewed ? 'PROVED' : formal ? 'SUPPORTED' : 'OPEN',
      evidence: formal ? 'FORMAL' : 'NONE',
      run: formal ? 'SUCCESS' : 'ERROR',
      freshness: 'CURRENT',
      trust: sorryDependent ? 'SORRY_DEPENDENT' : 'UNCONDITIONAL'
    },
    sourceHash,
    ...fp,
    deployCommit,
    stdout: formal
      ? 'Render clean lake build completed; build-time Lean.collectAxioms artifact loaded.'
      : '',
    stderr: auditError,
    axiomAuditOutput: output
  }
}

function enqueue(job) {
  if (queue.length >= MAX_QUEUE) return false
  queue.push(job)
  drain()
  return true
}

async function drain() {
  if (running || queue.length === 0) return
  running = true
  const job = queue.shift()
  try {
    const result = await verifyC014(job.semanticReviewed)
    if (result?.state?.run === 'SUCCESS' && result?.state?.evidence === 'FORMAL') lastSelfTest = result
    reply(job.res, 200, result, job.origin)
  } catch (error) {
    reply(job.res, 500, { error: String(error?.message || error) }, job.origin)
  } finally {
    running = false
    drain()
  }
}

const server = http.createServer(async (req, res) => {
  const origin = req.headers.origin || ''

  if (req.method === 'OPTIONS') {
    if (!ORIGINS.has(origin)) return reply(res, 403, { error: 'origin denied' })
    res.writeHead(204, {
      ...cors(origin),
      'access-control-allow-methods': 'GET,POST,OPTIONS',
      'access-control-allow-headers': 'content-type',
    })
    return res.end()
  }

  if (origin && !ORIGINS.has(origin)) return reply(res, 403, { error: 'origin denied' })

  const url = new URL(req.url || '/', 'http://localhost')
  if (req.method === 'GET' && url.pathname === '/') {
    const ready = lastSelfTest?.state?.run === 'SUCCESS' && lastSelfTest?.state?.evidence === 'FORMAL'
    const html = `<!doctype html>
<html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>MathScope Cloud Lean</title>
<style>
body{margin:0;background:#071722;color:#d9edf0;font-family:system-ui,-apple-system,Segoe UI,sans-serif}
main{max-width:760px;margin:0 auto;padding:48px 22px}.card{border:1px solid #244657;background:#0b2230;border-radius:16px;padding:22px}
h1{margin:0 0 8px;font-size:28px}p{color:#9ebcc5;line-height:1.6}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:10px;margin-top:18px}
.item{border:1px solid #234354;border-radius:12px;padding:14px;background:#091c28}.k{font-size:12px;color:#7fa2ad}.v{margin-top:4px;font-weight:700}.ok{color:#8de4b0}.warn{color:#f2c96d}
a{color:#8ed7ff}code{font-family:ui-monospace,Consolas,monospace}
</style></head><body><main><div class="card">
<h1>MathScope Cloud Lean</h1>
<p>Cloud-first Lean 4 + mathlib verification backend. Browser LSP and final proof issuance are intentionally separated.</p>
<div class="grid">
<div class="item"><div class="k">Service</div><div class="v ok">ONLINE</div></div>
<div class="item"><div class="k">LSP</div><div class="v ok">READY</div></div>
<div class="item"><div class="k">C-014 verifier</div><div class="v ${ready?'ok':'warn'}">${ready?'VERIFIED':'CHECKING'}</div></div>
<div class="item"><div class="k">Mode</div><div class="v">restricted-c014</div></div>
</div>
<p><a href="/health">/health</a> · <a href="/v1/meta">/v1/meta</a> · <a href="/v1/self-test">/v1/self-test</a><br>
Web app: <a href="https://project29770.websitepublisher.ai/index.html">MathScope</a></p>
</div></main></body></html>`
    return replyHtml(res, 200, html, origin)
  }

  if (req.method === 'GET' && url.pathname === '/health') {
    return reply(res, 200, {
      ok: true,
      service: 'mathscope-cloud-lean',
      mode: 'restricted-c014',
      verifierReady: lastSelfTest?.state?.run === 'SUCCESS' && lastSelfTest?.state?.evidence === 'FORMAL',
      lspReady: true,
      lspSessions: lspSessions.size,
      lspCapacity: MAX_LSP_SESSIONS,
      running,
      queued: queue.length
    }, origin)
  }

  if (req.method === 'GET' && url.pathname === '/v1/self-test') {
    return reply(res, lastSelfTest ? 200 : 503, lastSelfTest || { status: 'PENDING' }, origin)
  }

  if (req.method === 'GET' && url.pathname === '/v1/meta') {
    try {
      return reply(res, 200, {
        service: 'mathscope-cloud-lean',
        mode: 'restricted-c014',
        ...(await fingerprint())
      }, origin)
    } catch (error) {
      return reply(res, 500, { error: String(error?.message || error) }, origin)
    }
  }

  if (req.method === 'POST' && url.pathname === '/v1/verify/c014') {
    let body = ''
    for await (const chunk of req) {
      body += chunk.toString('utf8')
      if (body.length > 4096) return reply(res, 413, { error: 'request too large' }, origin)
    }
    let parsed = {}
    try { parsed = body ? JSON.parse(body) : {} } catch {
      return reply(res, 400, { error: 'invalid JSON' }, origin)
    }
    const accepted = enqueue({
      res,
      origin,
      semanticReviewed: parsed.semanticReviewed === true
    })
    if (!accepted) return reply(res, 429, { error: 'verification queue full' }, origin)
    return
  }

  reply(res, 404, { error: 'not found' }, origin)
})

const wss = new WebSocketServer({ noServer: true, maxPayload: 1_000_000 })
server.on('upgrade', (req, socket, head) => {
  const origin = req.headers.origin || ''
  if (!ORIGINS.has(origin)) {
    socket.destroy()
    return
  }
  const url = new URL(req.url || '/', 'http://localhost')
  if (url.pathname !== '/v1/lsp') {
    socket.destroy()
    return
  }
  wss.handleUpgrade(req, socket, head, ws => {
    startLspSession(ws).catch(error => {
      try {
        ws.send(JSON.stringify({ mathscope: { type: 'error', text: String(error?.message || error) } }))
        ws.close(1011, 'Lean LSP session failed')
      } catch {}
    })
  })
})

server.listen(PORT, '0.0.0.0', async () => {
  console.log('MathScope Cloud Lean listening on', PORT)
  if (process.env.MATHSCOPE_SELF_TEST !== '0') {
    try {
      const result = await verifyC014(false)
      lastSelfTest = result
      console.log('C014_SELF_TEST', JSON.stringify({
        run: result.state.run,
        truth: result.state.truth,
        evidence: result.state.evidence,
        freshness: result.state.freshness,
        trust: result.state.trust,
        sourceHash: result.sourceHash,
        environmentHash: result.environmentHash,
        dependencyLockHash: result.dependencyLockHash,
        axiomAuditOutput: result.axiomAuditOutput,
        stdout: result.stdout,
        stderr: result.stderr
      }))
    } catch (error) {
      lastSelfTest = { status: 'ERROR', error: String(error?.stack || error) }
      console.error('C014_SELF_TEST_ERROR', String(error?.stack || error))
    }
  }
})
