# PR Summary — Environment Variables

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

PR サマリ生成の挙動を制御する環境変数の一覧です。
- `ADAPTER_WARN_MAX` / `ADAPTER_ERROR_MAX`: アダプターの警告/エラー許容数
- `SUMMARY_MODE`: `digest` | `detailed`（通常はラベルで切替）
- `SUMMARY_LANG`: `en` | `ja`（既定 `en`）

ワークフローの `env:` で設定して使用します（下の英語セクション参照）。

- ADAPTER_WARN_MAX — maximum allowed adapter warnings count (default 0)
- ADAPTER_ERROR_MAX — maximum allowed adapter errors count (default 0)
- SUMMARY_MODE — digest | detailed (usually set via label pr-summary:detailed)

Usage (in workflow step)
```yaml
env:
  ADAPTER_WARN_MAX: 0
  ADAPTER_ERROR_MAX: 0
  SUMMARY_MODE: ${{ steps.mode.outputs.mode }}
```
- SUMMARY_LANG — en | ja (default en)
