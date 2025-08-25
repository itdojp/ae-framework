export function assertNever(x: never, msg = 'Unexpected case'): never {
  // 実行時保険（型漏れがあってもクラッシュで気づける）
  throw new Error(`${msg}: ${JSON.stringify(x)}`);
}