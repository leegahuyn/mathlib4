import test from 'node:test'
import assert from 'node:assert/strict'
import { spawn } from 'node:child_process'

test('HTTP boundary rejects submitted code and freshly verifies only the scoped Golden claim', { timeout: 180000 }, async () => {
  const port = 13269
  const child = spawn(process.execPath, ['server.mjs'], {
    cwd: new URL('.', import.meta.url), windowsHide: true,
    env: { ...process.env, PORT: String(port), MATHSCOPE_SELF_TEST: '0' },
    stdio: ['ignore', 'pipe', 'pipe'],
  })
  let stderr = ''
  child.stderr.on('data', chunk => { stderr += chunk })
  try {
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(Error('Server startup timed out: ' + stderr)), 10000)
      child.stdout.on('data', chunk => { if (String(chunk).includes('listening on')) { clearTimeout(timer); resolve() } })
      child.once('error', reject)
      child.once('exit', code => { clearTimeout(timer); reject(Error('Server exited ' + code + ': ' + stderr)) })
    })
    const base = `http://127.0.0.1:${port}`
    const origin = 'https://project29770.websitepublisher.ai'
    const metaResponse = await fetch(base + '/v1/golden/meta', { headers: { Origin: origin } })
    assert.equal(metaResponse.status, 200)
    assert.equal(metaResponse.headers.get('access-control-allow-origin'), origin)
    const meta = await metaResponse.json()
    const input = { claimId: meta.claimId, sourceHash: meta.sourceHash, semanticReviewed: true }
    const post = body => fetch(base + '/v1/verify/golden', { method: 'POST', headers: { 'content-type': 'application/json', Origin: origin }, body: typeof body === 'string' ? body : JSON.stringify(body) })
    for (const invalid of [null, { ...input, source: 'theorem fabricated : False := by sorry' }, { ...input, sourceHash: '0'.repeat(64) }, '{broken']) {
      const response = await post(invalid)
      assert.equal(response.status, 400, await response.text())
    }
    assert.equal((await post('x'.repeat(4097))).status, 413)
    const denied = await fetch(base + '/v1/golden/meta', { headers: { Origin: 'https://untrusted.example' } })
    assert.equal(denied.status, 403)
    const response = await post(input)
    assert.equal(response.status, 200)
    const result = await response.json()
    assert.equal(result.state.run, 'SUCCESS', JSON.stringify(result))
    assert.equal(result.state.truth, 'PROVED')
    assert.equal(result.sourceHash, meta.sourceHash)
    assert.equal(result.environmentHash, meta.environmentHash)
    assert.equal(result.dependencyLockHash, meta.dependencyLockHash)
    assert.equal(result.verificationMode, 'fresh-lean-process-per-request')
    assert.equal(result.excludedClaims.some(c => c.includes('PDE global existence')), true)
    // Golden proof must never replace the independent C014 self-test state.
    assert.equal((await fetch(base + '/v1/self-test')).status, 503)
  } finally {
    child.kill()
  }
})
