import test from 'node:test'
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { readFile } from 'node:fs/promises'
import { goldenMeta, verifyGolden, validGoldenAxiomAudit } from './golden-verifier.mjs'

const claimId = 'GOLDEN-NONLINEAR-ALGEBRA-001'
const sourceHash = '6e5dca8c5675e0c262d80ddd351b3cb6ea0ff5111b00873435893e3ed513daeb'
const input = { claimId, sourceHash, semanticReviewed: true }
const version = 'Lean (version 4.34.0-rc2, test-platform, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)'
const names = ['exact_perturbation', 'constant_one_stationary', 'constant_one_linear_coefficient']
const audit = names.map(n => `'MathScope.GoldenElliptic.${n}' depends on axioms: [propext, Classical.choice, Quot.sound]`).join('\n')
const good = { stdout: audit, stderr: '', code: 0, timedOut: false }
const runner = compilation => async args => args[0] === '--version'
  ? { stdout: version, stderr: '', code: 0, timedOut: false } : compilation

test('bundled audited source has the reviewed exact byte hash', async () => {
  const bytes = await readFile(new URL('./golden/GoldenAlgebra.lean', import.meta.url))
  assert.equal(createHash('sha256').update(bytes).digest('hex'), sourceHash)
  assert.equal(bytes.includes(Buffer.from('\r')), false)
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
