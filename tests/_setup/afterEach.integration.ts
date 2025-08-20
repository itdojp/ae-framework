import 'why-is-node-running'
import { afterEach, beforeEach } from 'vitest'

let beforeHandles = 0

beforeEach(() => {
  beforeHandles = (process as any)['_getActiveHandles']?.().length ?? 0
})

afterEach(async () => {
  // 最長5秒で停止させるラッパー
  async function stopWithTimeout(s: { stop: () => Promise<void> }) {
    return Promise.race([
      s.stop(),
      new Promise((_, rej) => setTimeout(() => rej(new Error('Shutdown timeout')), 5000)),
    ])
  }

  // グローバルに保持している最上位のシステムがあれば止める（テスト側が set）
  const sys = (globalThis as any).optimizationSystem
  if (sys?.stop) {
    try { await stopWithTimeout(sys) } catch (e) { /* ここでは握りつぶし */ }
  }

  // GC（Node起動に --expose-gc が必要）
  if (global.gc) { try { global.gc() } catch { /* noop */ } }

  const afterHandles = (process as any)['_getActiveHandles']?.().length ?? 0
  if (afterHandles > beforeHandles) {
    // 可視化（why-is-node-running が詳細を出す）
    // 次のフェーズへ流入しないように軽い警告を出す
    // 実際のfailはA11yやTDD Gateへ任せると良い
    // console.warn(`[leak] handles: ${beforeHandles} -> ${afterHandles}`)
  }
})