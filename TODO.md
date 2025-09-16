# TODO (短期)

- [ ] Actionlint 残差確認（workflow-lint で全通過）
- [ ] test:fast 再導入 第2弾の候補決定（影響小カテゴリから）
- [ ] Security/Compliance: PR コメント要約の自動投稿（任意、label 時）
- [ ] ae-ci: 失敗時の要約（失敗カテゴリ/所要時間）
- [ ] Docs: SECURITY.md/ci-policy の図版・簡易フロー追加（任意）

# Backlog（中期）

- [ ] hermetic-ci のログ整形（echo⇒printf の統一、要約出力）
- [ ] parallel-test-execution のアーティファクト一元化
- [ ] sbom-generation: 既知許容（allowlist）サンプルの docs 化
- [ ] codegen-drift-check: 失敗理由の PR コメント詳細化

# Done（このセッションで対応）

- Actionlint 主要差分修正（echo→printf、出力の安全化）
- QA CLI の追加（`ae qa --light`）と CI 反映
- SBOM/セキュリティのライセンス要約・閾値強制の段階導入
- test:fast へ `tests/utils/**` 再導入（第1弾）
- Docs 更新（ci-policy, benchmark light/dry-run, SECURITY 運用）
