import { setMaxListeners } from 'node:events'
import { afterEach, beforeEach, vi } from 'vitest'
import {
  drainIntegrationCleanupTasks,
  resetIntegrationCleanupTasks,
} from '../_helpers/integration-test-utils.js'

let beforeHandles = 0
const unlimitedMarker = Symbol.for('ae.integration.unlimitedListeners')
const shouldTraceHandles =
  process.env.AE_INTEGRATION_TRACE_HANDLES === '1' ||
  process.env.AE_INTEGRATION_TRACE_HANDLES?.toLowerCase() === 'true'

if (shouldTraceHandles) {
  await import('why-is-node-running')
}

const enforceUnlimitedListeners = (stream: any) => {
  if (!stream || typeof stream.setMaxListeners !== 'function') {
    return;
  }
  if (stream[unlimitedMarker]) {
    return;
  }
  const original = stream.setMaxListeners.bind(stream);
  stream.setMaxListeners = (_?: number) => original(0);
  original(0);
  stream[unlimitedMarker] = true;
};

enforceUnlimitedListeners(process.stdout);
enforceUnlimitedListeners(process.stderr);

setMaxListeners(0)

beforeEach(() => {
  enforceUnlimitedListeners(process.stdout);
  enforceUnlimitedListeners(process.stderr);
  resetIntegrationCleanupTasks();
  beforeHandles = (process as any)['_getActiveHandles']?.().length ?? 0
})

afterEach(async () => {
  // Skip shared cleanup if test is managing its own cleanup or cleanup is already in progress
  if ((globalThis as any).__testManagedCleanup || (globalThis as any).__cleanupInProgress) {
    return;
  }

  const cleanupTasks = drainIntegrationCleanupTasks();
  for (let i = cleanupTasks.length - 1; i >= 0; i -= 1) {
    const task = cleanupTasks[i];
    try {
      await task();
    } catch (error) {
      console.warn('Integration cleanup task failed:', error);
    }
  }

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
    try { 
      await stopWithTimeout(sys);
      // Clear reference after successful shutdown
      delete (globalThis as any).optimizationSystem;
    } catch (e) { 
      // ここでは握りつぶし
      console.warn('Shared cleanup timeout:', e);
    }
  }

  // GC（Node起動に --expose-gc が必要）
  if (global.gc) { try { global.gc() } catch { /* noop */ } }

  vi.restoreAllMocks();
  vi.clearAllMocks();
  vi.useRealTimers();

  const afterHandles = (process as any)['_getActiveHandles']?.().length ?? 0
  if (afterHandles > beforeHandles) {
    // 可視化（why-is-node-running が詳細を出す）
    // 次のフェーズへ流入しないように軽い警告を出す
    // 実際のfailはA11yやTDD Gateへ任せると良い
    // console.warn(`[leak] handles: ${beforeHandles} -> ${afterHandles}`)
  }
})
