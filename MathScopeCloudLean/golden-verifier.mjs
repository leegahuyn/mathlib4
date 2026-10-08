import { spawn } from 'node:child_process'
import { createHash, randomUUID } from 'node:crypto'
import { readFile } from 'node:fs/promises'
import path from 'node:path'
import { fileURLToPath } from 'node:url'

const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), 'golden')
const CLAIM = 'GOLDEN-NONLINEAR-ALGEBRA-001'
const MODE = 'restricted-golden-algebra'
const TOOLCHAIN = 'leanprover/lean4:v4.34.0-rc2'
const LEAN_COMMIT = '6a10ac8c22beadecabdbb0919c2b50214762f91d'
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const THEOREMS = ['exact_perturbation', 'constant_one_stationary', 'constant_one_linear_coefficient'].map(n => 'MathScope.GoldenElliptic.' + n)
const ALLOWED_AXIOMS = ['Classical.choice', 'Quot.sound', 'propext']
const invalidInput = message => Object.assign(new Error(message), { statusCode: 400 })

export function runLean(args, { env = process.env, timeoutMs = 90000, leanCommand = 'lean' } = {}) {
  return new Promise(resolve => {
    let stdout = '', stderr = '', settled = false
    const child = spawn(leanCommand, args, { cwd: ROOT, env, shell: false, windowsHide: true, detached: process.platform !== 'win32', stdio: ['ignore', 'pipe', 'pipe'] })
    const finish = result => { if (settled) return; settled = true; clearTimeout(timer); resolve({ stdout, stderr, ...result }) }
    const timer = setTimeout(() => {
      try { if (process.platform === 'win32') child.kill(); else process.kill(-child.pid, 'SIGKILL') } catch { child.kill() }
      finish({ code: null, timedOut: true })
    }, timeoutMs)
    child.stdout.on('data', chunk => { if (stdout.length < 200000) stdout += chunk.toString('utf8') })
    child.stderr.on('data', chunk => { if (stderr.length < 200000) stderr += chunk.toString('utf8') })
    child.on('error', error => { stderr += String(error.message || error); finish({ code: null, timedOut: false }) })
    child.on('close', code => finish({ code, timedOut: false }))
  })
}

export function validGoldenAxiomAudit(stdout) {
  const rows = [...stdout.matchAll(/'([^']+)' depends on axioms: \[([^\]]*)\]/g)]
  if (rows.length !== THEOREMS.length || /sorryAx/.test(stdout)) return false
  return THEOREMS.every(name => {
    const matching = rows.filter(row => row[1] === name)
    return matching.length === 1 && JSON.stringify(matching[0][2].split(',').map(x => x.trim()).filter(Boolean).sort()) === JSON.stringify(ALLOWED_AXIOMS)
  })
}

async function target() {
  const [sourceBytes, manifestBytes, toolchainBytes] = await Promise.all(['GoldenAlgebra.lean', 'golden-manifest.json', 'lean-toolchain'].map(n => readFile(path.join(ROOT, n))))
  const manifest = JSON.parse(manifestBytes.toString('utf8'))
  const sourceHash = sha(sourceBytes)
  if (manifest.claimId !== CLAIM || manifest.sourceHash !== sourceHash || toolchainBytes.toString('utf8').trim() !== TOOLCHAIN) throw Error('Golden source/toolchain integrity failure')
  return { source: sourceBytes.toString('utf8'), sourceHash, manifest, dependencyLockHash: sha(manifestBytes) }
}

export async function goldenMeta(options = {}) {
  const t = await target(), runner = options.runner || runLean
  const version = await runner(['--version'], { ...options, timeoutMs: 10000 })
  const leanVersion = version.stdout.trim()
  if (version.code !== 0 || version.timedOut || !leanVersion.includes('version 4.34.0-rc2,') || !leanVersion.includes(LEAN_COMMIT)) throw Error('Pinned Golden Lean runtime unavailable or changed')
  const environmentHash = sha(JSON.stringify({ toolchain: TOOLCHAIN, leanVersion, dependencies: 'Lean core only; no external packages' }))
  return {
    service: 'mathscope-cloud-lean', mode: MODE, claimId: CLAIM,
    source: t.source, sourceHash: t.sourceHash, toolchain: TOOLCHAIN, leanVersion,
    environmentHash, dependencyLockHash: t.dependencyLockHash,
    deployCommit: process.env.RENDER_GIT_COMMIT || null,
    verificationMode: 'fresh-lean-process-per-request', formalScope: t.manifest.formalScope,
    assumptions: t.manifest.assumptions, excludedClaims: t.manifest.excludedClaims,
    theoremNames: THEOREMS, expectedAxioms: ALLOWED_AXIOMS,
  }
}

export async function verifyGolden(input, options = {}) {
  if (!input || typeof input !== 'object' || Array.isArray(input) || Object.keys(input).some(k => !['claimId', 'sourceHash', 'semanticReviewed'].includes(k))) throw invalidInput('Only claimId, sourceHash and semanticReviewed are accepted; arbitrary source is forbidden')
  const current = await target()
  if (input.claimId !== CLAIM || input.sourceHash !== current.sourceHash || typeof input.semanticReviewed !== 'boolean') throw invalidInput('Golden claim/source binding or semantic review flag invalid')
  const meta = await goldenMeta(options), started = Date.now(), runner = options.runner || runLean
  // This always starts Lean against the fixed audited source. No cached proof artifact is accepted.
  const compilation = await runner(['GoldenAlgebra.lean'], options)
  const formal = compilation.code === 0 && !compilation.timedOut && compilation.stderr.trim() === '' && validGoldenAxiomAudit(compilation.stdout)
  const axiomAuditOutput = compilation.stdout.trim()
  return {
    id: randomUUID(), createdAt: new Date().toISOString(), ...meta,
    state: { run: formal ? 'SUCCESS' : compilation.timedOut ? 'TIMEOUT' : 'ERROR', evidence: formal ? 'FORMAL' : 'NONE', truth: formal && input.semanticReviewed ? 'PROVED' : formal ? 'SUPPORTED' : 'OPEN', freshness: 'CURRENT', trust: formal ? 'UNCONDITIONAL' : 'UNVERIFIED' },
    sourceArtifactCommit: process.env.RENDER_GIT_COMMIT || null,
    elapsedMs: Date.now() - started, exitCode: compilation.code, timedOut: compilation.timedOut,
    stdout: compilation.stdout, stderr: compilation.stderr, axiomAuditOutput,
    proofHash: formal ? sha(JSON.stringify({ sourceHash: meta.sourceHash, environmentHash: meta.environmentHash, axiomAuditOutput })) : null,
  }
}
