import http from 'node:http'
import { spawn } from 'node:child_process'
import { createHash, randomUUID } from 'node:crypto'
import { mkdir, readFile, rm, writeFile } from 'node:fs/promises'
import path from 'node:path'

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
let running = false
const queue = []

function sha256(value) {
  return createHash('sha256').update(value).digest('hex')
}

function leanEnv() {
  const home = process.env.HOME || ''
  const elan = path.join(home, '.elan', 'bin')
  const current = process.env.PATH || ''
  return { ...process.env, PATH: [elan, current].filter(Boolean).join(path.delimiter) }
}

function cors(origin) {
  return origin && ORIGINS.has(origin)
    ? { 'access-control-allow-origin': origin, 'vary': 'Origin' }
    : {}
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
      running,
      queued: queue.length
    }, origin)
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

server.listen(PORT, '0.0.0.0', () => {
  console.log('MathScope Cloud Lean listening on', PORT)
})
