# Issue 1225: Security Alert Inventory (2026-01)

## Snapshot
- Commit: f44ff049
- Source: package.json / pnpm.overrides / workflow action config

## Versions in repo (targeted by #1225)
| package | version | source | note |
| --- | --- | --- | --- |
| @modelcontextprotocol/sdk | ^1.25.1 | dependencies | 0.x系から更新済み（PR #1337） |
| esbuild | 0.27.2 | pnpm.overrides | Go stdlib 脆弱性対策の一環（PR #1338） |
| glob | ^10.5.0 | dependencies | CodeQL/Trivy対象の棚卸し用に現状値を記録 |
| js-yaml | ^4.1.1 | dependencies | 4.1.0系のCVE対応（PR #1241） |
| qs | 6.14.1 | pnpm.overrides | CVE-2025-15284 対応（PR #1340） |
| npm | >=10.5.0 | .github/actions/setup-pnpm/action.yml | CIのnpm最小バージョンを引き上げ（PR #1339） |

## Notes
- Trivy/Code Scanning 側のアラート解消可否は、Security/SBOM ワークフロー再実行の結果で確認する。
- 新たな警告が出た場合はこの表に追記して小粒PRへ分割する。
