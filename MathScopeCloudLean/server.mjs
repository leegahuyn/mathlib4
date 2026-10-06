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
  const sessionDir = path.join(ROOT, '.mathscope-cloud', 'lsp', sessionId)
  const documentPath = path.join(sessionDir, 'Main.lean')
  await mkdir(sessionDir, { recursive: true })
  await writeFile(documentPath, 'import Mathlib\n', 'utf8')

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
    rm(sessionDir, { recursive: true, force: true }).catch(() => {})
  }

  const refreshIdle = () => {
    if (session.timer) clearTimeout(session.timer)
    session.timer = setTimeout(() => {
      try { ws.close(1000, 'Lean LSP idle timeout') } catch {}
      cleanup()
    }, LSP_IDLE_MS)
  }

  const framer = new LspFramer(message => {
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

  const direct = await run('lake', ['env', 'lean', 'MathScope/Claims/C014.lean'], ROOT)
  if (direct.timedOut || direct.code !== 0) {
    return {
      id,
      claimId: 'C-014',
      createdAt: new Date().toISOString(),
      state: {
        truth: 'OPEN',
        evidence: 'NONE',
        run: direct.timedOut ? 'TIMEOUT' : 'ERROR',
        freshness: 'CURRENT',
        trust: 'UNCONDITIONAL'
      },
      sourceHash,
      ...fp,
      stdout: direct.stdout,
      stderr: direct.stderr,
      axiomAuditOutput: ''
    }
  }

  const auditDir = path.join(ROOT, '.mathscope-cloud')
  await mkdir(auditDir, { recursive: true })
  const auditRel = path.join('.mathscope-cloud', 'audit-' + id + '.lean')
  const auditFull = path.join(ROOT, auditRel)
  await writeFile(
    auditFull,
    'import MathScope.Claims.C014\n#print axioms MathScope.Claims.C014.c014_slice_radius\n',
    'utf8'
  )
  const audit = await run('lake', ['env', 'lean', auditRel], ROOT)
  await rm(auditFull, { force: true })

  const output = (audit.stdout + '\n' + audit.stderr).trim()
  const sorryDependent = /sorryAx/.test(output)
  const formal = audit.code === 0 && !audit.timedOut
  return {
    id,
    claimId: 'C-014',
    createdAt: new Date().toISOString(),
    state: {
      truth: formal && semanticReviewed && !sorryDependent ? 'PROVED' : formal ? 'SUPPORTED' : 'OPEN',
      evidence: formal ? 'FORMAL' : 'NONE',
      run: audit.timedOut ? 'TIMEOUT' : audit.code === 0 ? 'SUCCESS' : 'ERROR',
      freshness: 'CURRENT',
      trust: sorryDependent ? 'SORRY_DEPENDENT' : 'UNCONDITIONAL'
    },
    sourceHash,
    ...fp,
    stdout: direct.stdout,
    stderr: direct.stderr + (audit.stderr ? '\n' + audit.stderr : ''),
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
