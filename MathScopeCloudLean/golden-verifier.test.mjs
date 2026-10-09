import test from 'node:test'
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { copyFile, mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { pathToFileURL } from 'node:url'
import { goldenMeta, verifyGolden, validGoldenAxiomAudit } from './golden-verifier.mjs'

const claimId = 'GOLDEN-NONLINEAR-ALGEBRA-001'
const sourceHash = 'd27a3c8baa37889217d546a9020ea54552e850888590739062300821406ce593'
const input = { claimId, sourceHash, semanticReviewed: true }
const version = 'Lean (version 4.34.0-rc2, test-platform, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)'
const names = ['exact_perturbation', 'constant_one_stationary', 'constant_one_linear_coefficient']
const audit = names.map(n => `'MathScope.GoldenElliptic.${n}' depends on axioms: [propext, Classical.choice, Quot.sound]`).join('\n')
const good = { stdout: audit, stderr: '', code: 0, timedOut: false }
const runner = compilation => async args => args[0] === '--version'
  ? { stdout: version, stderr: '', code: 0, timedOut: false } : compilation

async function copyGoldenPackage(t) {
  const temporaryRoot = path.resolve(tmpdir())
  const directory = await mkdtemp(path.join(temporaryRoot, 'mathscope-golden-test-'))
  t.after(async () => {
    assert.equal(path.dirname(directory), temporaryRoot)
    assert.match(path.basename(directory), /^mathscope-golden-test-/)
    await rm(directory, { recursive: true, force: true })
  })
  await mkdir(path.join(directory, 'golden'))
  for (const name of ['golden-verifier.mjs', 'golden/GoldenAlgebra.lean', 'golden/golden-manifest.json', 'golden/lean-toolchain']) {
    await copyFile(new URL(name, import.meta.url), path.join(directory, name))
  }
  return { directory, verifier: await import(pathToFileURL(path.join(directory, 'golden-verifier.mjs')).href) }
}

async function rejectsPackageBeforeLean(verifier, request = input) {
  const calls = []
  const options = { runner: async args => { calls.push(args); return runner(good)(args) } }
  const outcomes = await Promise.allSettled([verifier.goldenMeta(options), verifier.verifyGolden(request, options)])
  assert.deepEqual(calls, [], 'Package integrity must fail before any Lean invocation')
  for (const outcome of outcomes) {
    assert.equal(outcome.status, 'rejected', 'An altered package must not return metadata or a FORMAL receipt')
    assert.match(outcome.reason.message, /integrity failure/)
  }
}

test('bundled audited source has the reviewed exact byte hash', async () => {
  const bytes = await readFile(new URL('./golden/GoldenAlgebra.lean', import.meta.url))
  assert.equal(createHash('sha256').update(bytes).digest('hex'), sourceHash)
  assert.equal(bytes.includes(Buffer.from('\r')), false)
})

for (const [field, value] of [
  ['schema', 'MathScopeGoldenFormal/999'],
  ['claimId', 'UNREVIEWED-CLAIM'],
  ['sourceHash', '0'.repeat(64)],
  ['toolchain', 'leanprover/lean4:v0.0.0'],
  ['dependencies', ['unreviewed-package']],
  ['formalScope', 'Full PDE global existence and uniqueness'],
  ['assumptions', []],
  ['excludedClaims', []],
  ['extraClaim', 'Unreviewed theorem'],
]) {
  test(`package integrity rejects changed manifest ${field} before Lean`, async t => {
    const { directory, verifier } = await copyGoldenPackage(t)
    const manifestPath = path.join(directory, 'golden/golden-manifest.json')
    const manifest = JSON.parse(await readFile(manifestPath, 'utf8'))
    manifest[field] = value
    await writeFile(manifestPath, JSON.stringify(manifest))
    await rejectsPackageBeforeLean(verifier)
  })
}

test('package integrity pins full manifest bytes and rejects malformed manifests', async t => {
  const { directory, verifier } = await copyGoldenPackage(t)
  const manifestPath = path.join(directory, 'golden/golden-manifest.json')
  const original = await readFile(manifestPath)
  for (const bytes of [Buffer.concat([original, Buffer.from('\n')]), Buffer.from('{}'), Buffer.from('{invalid'), Buffer.from([0xff])]) {
    await writeFile(manifestPath, bytes)
    await rejectsPackageBeforeLean(verifier)
  }
})

for (const rehashManifest of [false, true]) {
  test(`package integrity rejects altered source${rehashManifest ? ' with coordinated manifest self-rehash' : ''}`, async t => {
    const { directory, verifier } = await copyGoldenPackage(t)
    const sourcePath = path.join(directory, 'golden/GoldenAlgebra.lean')
    const source = Buffer.concat([await readFile(sourcePath), Buffer.from('\n-- altered package\n')])
    await writeFile(sourcePath, source)
    const request = { ...input }
    if (rehashManifest) {
      const manifestPath = path.join(directory, 'golden/golden-manifest.json')
      const manifest = JSON.parse(await readFile(manifestPath, 'utf8'))
      request.sourceHash = manifest.sourceHash = createHash('sha256').update(source).digest('hex')
      await writeFile(manifestPath, JSON.stringify(manifest))
    }
    await rejectsPackageBeforeLean(verifier, request)
  })
}

test('package integrity rejects an altered toolchain before Lean', async t => {
  const { directory, verifier } = await copyGoldenPackage(t)
  await writeFile(path.join(directory, 'golden/lean-toolchain'), 'leanprover/lean4:v0.0.0\n')
  await rejectsPackageBeforeLean(verifier)
})

test('arbitrary source, executable, path and malformed claim inputs cannot start Lean', async () => {
  let calls = 0
  const options = { runner: async () => { calls++; return good } }
  for (const invalid of [null, [], {}, { ...input, source: 'example : False := by sorry' },
    { ...input, leanCommand: 'untrusted' }, { ...input, sourcePath: '../../evil.lean' },
    { ...input, sourceHash: '0'.repeat(64) }, { ...input, claimId: 'C-014' },
    { ...input, semanticReviewed: 'true' }]) {
    await assert.rejects(verifyGolden(invalid, options), { statusCode: 400 })
  }
  assert.equal(calls, 0)
})

test('semantic review changes only truth for a successfully verified fixed claim', async () => {
  const result = await verifyGolden({ ...input, semanticReviewed: false }, { runner: runner(good) })
  assert.equal(result.state.evidence, 'FORMAL')
  assert.equal(result.state.truth, 'SUPPORTED')
  assert.equal(result.formalScope.includes('not a full PDE theorem'), true)
  assert.equal(result.excludedClaims.some(c => c.includes('existence')), true)
})

test('wrong Lean toolchain or runtime commit fails before compilation', async () => {
  for (const stdout of [version.replace('4.34.0-rc2', '4.33.0'), version.replace('6a10ac8', '0000000')]) {
    await assert.rejects(verifyGolden(input, { runner: async () => ({ ...good, stdout }) }), /runtime unavailable or changed/)
  }
})

test('exit failure, timeout, stderr, missing audit and sorry-dependent proofs fail closed', async () => {
  const failures = [
    { ...good, code: 1 }, { ...good, timedOut: true }, { ...good, stderr: 'error' },
    { ...good, stdout: '' }, { ...good, stdout: audit.split('\n').slice(1).join('\n') },
    { ...good, stdout: audit.replace('propext', 'sorryAx') },
    { ...good, stdout: audit.replace('propext', 'untrustedAxiom') },
    { ...good, stdout: audit + '\n' + audit.split('\n')[0] },
  ]
  for (const compilation of failures) {
    const result = await verifyGolden(input, { runner: runner(compilation) })
    assert.equal(result.state.evidence, 'NONE')
    assert.equal(result.state.truth, 'OPEN')
    assert.equal(result.proofHash, null)
  }
})

test('axiom audit identifies all exact theorem names and ordinary kernel axioms', () => {
  assert.equal(validGoldenAxiomAudit(audit), true)
  assert.equal(validGoldenAxiomAudit(audit.replace('exact_perturbation', 'other_theorem')), false)
})

test('real Lean compiles twice freshly and produces a replay-identical proof hash', { timeout: 180000 }, async () => {
  const options = process.env.MATHSCOPE_TEST_LEAN ? { leanCommand: process.env.MATHSCOPE_TEST_LEAN } : {}
  const meta = await goldenMeta(options)
  const first = await verifyGolden(input, options)
  const second = await verifyGolden(input, options)
  for (const result of [first, second]) {
    assert.equal(result.state.run, 'SUCCESS', JSON.stringify(result))
    assert.equal(result.state.evidence, 'FORMAL')
    assert.equal(result.state.truth, 'PROVED')
    assert.equal(result.exitCode, 0)
    assert.equal(result.timedOut, false)
    assert.equal(result.sourceHash, meta.sourceHash)
    assert.equal(result.environmentHash, meta.environmentHash)
    assert.equal(result.verificationMode, 'fresh-lean-process-per-request')
    assert.equal(validGoldenAxiomAudit(result.axiomAuditOutput), true)
  }
  assert.notEqual(first.id, second.id)
  assert.equal(first.proofHash, second.proofHash)
})
