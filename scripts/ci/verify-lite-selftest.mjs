#!/usr/bin/env node
// Minimal self-test for Verify Lite (repo-local). Non-blocking.
function log(k, v) { process.stdout.write(`${k}: ${v}\n`) }
try {
  log('verify-lite-selftest', 'starting')
  log('node.version', process.version)
  log('platform', `${process.platform} ${process.arch}`)
  log('cwd', process.cwd())
  log('summary', 'ok')
  process.exit(0)
} catch (e) {
  console.error('selftest-error', e && e.message ? e.message : String(e))
  process.exit(0)
}

