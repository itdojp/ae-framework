# Security Policy / セキュリティポリシー

> 🌍 Language / 言語: English | 日本語

---

## English

### Supported Versions

Currently supported versions for security updates:

| Version | Supported          |
| ------- | ------------------ |
| 1.x.x   | ✅ Yes             |
| < 1.0   | ❌ No              |

### Reporting a Vulnerability

We take security vulnerabilities seriously. If you discover a security issue, please follow these steps:

1) Do NOT create a public GitHub issue
- Security vulnerabilities should be reported privately to avoid exposing the issue before a fix is available.

2) Contact us directly
- Email: security@ae-framework.dev (preferred)
- GitHub Security Advisory: Use GitHub's private vulnerability reporting feature

3) Include detailed information
- Description of the vulnerability
- Steps to reproduce the issue
- Potential impact assessment
- Suggested fix (if you have one)
- Your contact information

4) Response timeline
- Initial response: Within 24 hours
- Assessment: Within 72 hours
- Fix timeline: Depends on severity
  - Critical: 1-7 days
  - High: 1-14 days
  - Medium: 1-30 days
  - Low: Next scheduled release

### CI Security/Compliance Operations

- On pull requests, security jobs run non-blocking by default and publish artifacts for review. Heavy jobs are label/path gated per CI policy (see `docs/ci-policy.md` Path Conditions for configuration tips).
  - Tip: use `paths-ignore` (e.g., `docs/**`, `**/*.md`) to skip heavy scans on docs-only changes
- Labels:
  - `run-security` — opt-in Security/SBOM execution on PRs (posts a non-blocking summary comment)
  - `enforce-security` — enforce thresholds (blocking when limits exceeded)
- `ci-non-blocking` — continue-on-error for selected jobs when troubleshooting
  - Many security jobs honor this by setting `continue-on-error` when the label is present on PRs
  - Slash commands: `/run-security`, `/enforce-security` (see `.github/workflows/agent-commands.yml`)
  - Dispatch: `/run-security-dispatch` — triggers `sbom-generation.yml` on the PR head branch
  - Artifacts: `security-report`, `license-report` (default retention ~30 days)
  - CodeQL results: visible under GitHub "Security → Code scanning alerts" (not uploaded as artifacts by default)
- Local quickstart
  - `pnpm -s security:scan` — run local security scan
  - `pnpm -s security:config` — show current security config
 - Thresholds are configurable via repository variables (Settings → Variables → Repository variables):
  - `SECURITY_MAX_HIGH` (default 0): allowed High/Critical vulnerabilities
  - `SECURITY_MAX_MODERATE` (default 2): allowed Moderate vulnerabilities
- Workflow reference: `.github/workflows/sbom-generation.yml` generates SBOM, runs dependency audit, performs CodeQL, and optionally enforces thresholds. See also `.github/workflows/security.yml`.
  - Branch protection: when enforcing on `main`, add selected security checks as Required status checks under Settings → Branches → main → Require status checks
  - Schedule: daily security scan at 02:00 UTC (see `security.yml` `schedule`)

PR comment example (non-blocking when `run-security`)

```
Security Summary
High/Critical: 0 (limit: SECURITY_MAX_HIGH=0)
Moderate: 1 (limit: SECURITY_MAX_MODERATE=2)
Policy: report-only (apply `enforce-security` to gate)
Links: .github/workflows/sbom-generation.yml, docs/ci-policy.md
```

References
- CI policy (label/path gating, Verify Lite defaults): `docs/ci-policy.md`
- Slash command mappings: `.github/workflows/agent-commands.yml`

### Security Measures

Automated Security Scanning
- Dependency scanning: `npm audit` runs on every CI build
- Secret detection: Gitleaks scans for exposed credentials
- Code analysis: CodeQL security analysis (when available)
- Container scanning: Docker images scanned for vulnerabilities

Development Practices
- All dependencies are regularly updated
- Security linting rules are enforced
- Code review required for all changes
- Principle of least privilege applied
- Input validation and sanitization implemented

Infrastructure Security
- All communications use HTTPS/TLS
- Environment variables for sensitive configuration
- No hardcoded credentials in source code
- Regular security audits and penetration testing

### Security Architecture

Authentication & Authorization
- Token-based authentication
- Role-based access control (RBAC)
- Session management with secure defaults
- API rate limiting implemented

Data Protection
- Encryption at rest and in transit
- PII data handling compliance
- Secure backup procedures
- Data retention policies enforced

Monitoring & Logging
- Security event logging
- Anomaly detection
- Incident response procedures
- Regular security metrics review

### Vulnerability Disclosure

Responsible Disclosure
1. Report received and acknowledged
2. Vulnerability confirmed and assessed
3. Fix developed and tested
4. Security advisory published
5. CVE assigned (if applicable)
6. Recognition provided to reporter

Bug Bounty
- We currently do not have a formal bug bounty program, but we recognize and appreciate security researchers who help improve our security posture.

### Security Tools

Required Tools
- `npm audit` - Dependency vulnerability scanning
- `gitleaks` - Secret detection
- ESLint security rules
- GitHub Security Advisories

Recommended Tools
- CodeQL - Static analysis security testing
- Helmet.js - Security headers
- express-rate-limit - API rate limiting
- CORS - Cross-origin resource sharing

### Security Checklist

For Developers
- [ ] Run `npm run security:scan` before committing
- [ ] Never commit secrets or credentials
- [ ] Use environment variables for configuration
- [ ] Validate all inputs and sanitize outputs
- [ ] Follow secure coding guidelines
- [ ] Keep dependencies updated

For Deployments
- [ ] All security tools passing
- [ ] Environment variables configured
- [ ] HTTPS/TLS properly configured
- [ ] Security headers implemented
- [ ] Monitoring and logging enabled
- [ ] Backup and recovery tested

### Incident Response

Classification
- Critical: Immediate threat to data confidentiality, integrity, or availability
- High: Significant security impact requiring urgent attention
- Medium: Important security issue requiring timely resolution
- Low: Minor security improvement or hardening opportunity

Response Team
- Security Lead: [security@ae-framework.dev]
- Development Lead: [dev@ae-framework.dev]
- Infrastructure Lead: [ops@ae-framework.dev]

Communication
- Internal: Slack #security-incidents
- External: Security advisory via GitHub
- Users: Release notes and documentation updates

### Compliance

Standards Followed
- OWASP Top 10 Web Application Security Risks
- NIST Cybersecurity Framework
- Common Vulnerability Scoring System (CVSS)
- Software Package Data Exchange (SPDX)

Regular Assessments
- Quarterly security reviews
- Annual penetration testing
- Continuous dependency monitoring
- Regular security training for team

### Resources

Security Documentation
- OWASP Secure Coding Practices
- Node.js Security Best Practices
- GitHub Security Best Practices
 - Integrated security audit runbook: `docs/integrated-security-audit.md`

Contact Information
- Security Team: security@ae-framework.dev
- General Contact: contact@ae-framework.dev
- GitHub Security: Use private vulnerability reporting

---

## 日本語

### 対応バージョン

現在、セキュリティ更新の対象としてサポートしているバージョン：

| バージョン | サポート状況 |
| ---------- | ------------- |
| 1.x.x      | ✅ 対応       |
| < 1.0      | ❌ 非対応     |

### 脆弱性の報告

セキュリティ脆弱性は重大と捉えています。発見した場合は以下の手順に従ってください。

1) 公開の GitHub Issue を作成しないでください
- 修正が提供される前に情報が露出するのを避けるため、非公開で報告してください。

2) 直接ご連絡ください
- メール: security@ae-framework.dev（推奨）
- GitHub Security Advisory: GitHub の非公開脆弱性報告機能をご利用ください

3) 詳細情報を添えてください
- 脆弱性の説明
- 再現手順
- 影響の評価
- 可能であれば修正案
- 連絡先情報

4) 目安となる対応時間
- 初期応答: 24時間以内
- 評価: 72時間以内
- 修正の提供: 深刻度に依存
  - クリティカル: 1〜7日
  - 高: 1〜14日
  - 中: 1〜30日
  - 低: 次回の定期リリース

### セキュリティ対策

自動セキュリティスキャン
- 依存関係スキャン: `npm audit` を CI の各ビルドで実行
- シークレット検出: Gitleaks による漏えい検出
- コード解析: CodeQL による静的解析（利用可能な場合）
- コンテナスキャン: Docker イメージの脆弱性検査

開発プラクティス
- 依存関係は定期的に更新
- セキュリティに関する Lint ルールを適用
- 全ての変更はコードレビュー必須
- 最小権限の原則を適用
- 入力検証とサニタイズを実装

インフラセキュリティ
- すべての通信は HTTPS/TLS を使用
- 機密設定は環境変数で管理
- ソースコードに認証情報をハードコーディングしない
- 定期的なセキュリティ監査とペネトレーションテストを実施

### セキュリティアーキテクチャ

認証・認可
- トークンベース認証
- RBAC（ロールベースアクセス制御）
- セキュアなデフォルトのセッション管理
- API レート制限の実装

データ保護
- 透過的・保存時の暗号化
- 個人情報（PII）に関するコンプライアンス
- セキュアなバックアップ
- データ保持ポリシーの順守

監視・ログ
- セキュリティイベントのロギング
- 異常検知
- インシデント対応手順
- 定期的なセキュリティ指標のレビュー

### 脆弱性開示

責任ある開示
1. 報告を受領し、受付を通知
2. 脆弱性の確認と評価
3. 修正を開発・テスト
4. セキュリティアドバイザリを公開
5. 必要に応じて CVE を割り当て
6. 報告者への謝辞を掲載

バグバウンティ
- 公式なバグバウンティプログラムは現在ありませんが、セキュリティ向上へのご協力に感謝します。

### セキュリティツール

必須ツール
- `npm audit` - 依存関係の脆弱性スキャン
- `gitleaks` - シークレット検出
- ESLint のセキュリティルール
- GitHub Security Advisories

推奨ツール
- CodeQL - 静的解析セキュリティテスト
- Helmet.js - セキュリティヘッダー
- express-rate-limit - API レート制限
- CORS - クロスオリジンリソース共有

### セキュリティチェックリスト

開発者向け
- [ ] コミット前に `npm run security:scan` を実行
- [ ] 認証情報・シークレットをコミットしない
- [ ] 設定は環境変数で管理
- [ ] 全入力を検証し、出力をサニタイズ
- [ ] 安全なコーディングガイドラインに従う
- [ ] 依存関係を最新に保つ

デプロイ向け
- [ ] すべてのセキュリティツールがパスしている
- [ ] 環境変数が適切に設定されている
- [ ] HTTPS/TLS が正しく構成されている
- [ ] セキュリティヘッダーを実装
- [ ] 監視とロギングを有効化
- [ ] バックアップとリカバリを検証

### インシデント対応

分類
- クリティカル: 機密性・完全性・可用性への即時の脅威
- 高: 迅速な対応を要する重大な影響
- 中: 速やかな解決が望ましい重要課題
- 低: 小規模な改善やハードニングの機会

対応チーム
- Security Lead: [security@ae-framework.dev]
- Development Lead: [dev@ae-framework.dev]
- Infrastructure Lead: [ops@ae-framework.dev]

コミュニケーション
- 内部: Slack #security-incidents
- 外部: GitHub を通じたセキュリティアドバイザリ
- ユーザー: リリースノートやドキュメント更新

### コンプライアンス

準拠基準
- OWASP Top 10 Web Application Security Risks
- NIST Cybersecurity Framework
- CVSS（共通脆弱性評価システム）
- SPDX（ソフトウェア部品表）

定期評価
- 四半期ごとのセキュリティレビュー
- 年次ペネトレーションテスト
- 継続的な依存関係モニタリング
- チームへの定期的なセキュリティトレーニング

### 参考情報

セキュリティドキュメント
- OWASP Secure Coding Practices
- Node.js Security Best Practices
- GitHub Security Best Practices
 - 統合セキュリティ監査のランブック: `docs/integrated-security-audit.md`

連絡先
- セキュリティチーム: security@ae-framework.dev
- 一般窓口: contact@ae-framework.dev
- GitHub セキュリティ: 非公開脆弱性報告機能をご利用ください

---

Last Updated / 最終更新: January 2025
Next Review / 次回見直し: July 2025
### CI におけるセキュリティ/コンプライアンス運用

- PR では既定でセキュリティ関連ジョブを非ブロッキングで実行し、結果をアーティファクトに集約します。重いジョブはラベル/パス条件で制御します（label/path gated。詳細は `docs/ci-policy.md`）。
  - 補足: ドキュメントのみの変更では `paths-ignore`（例: `docs/**`, `**/*.md`）を活用して重いスキャンを回避
- ラベル運用:
  - `run-security` — PR で Security/SBOM を実行（非ブロッキングの要約コメントを投稿）
  - `enforce-security` — 閾値を強制（超過時はブロック）
  - `ci-non-blocking` — トラブルシュート時などに continue-on-error で一部ジョブを非ブロッキング化
- スラッシュコマンド: `/run-security`, `/enforce-security`（`.github/workflows/agent-commands.yml` を参照）
 - ディスパッチ: `/run-security-dispatch` — PR の head ブランチで `sbom-generation.yml` を起動
 - アーティファクト: `security-report`, `license-report`（既定の保持期間は約30日）
 - CodeQL の結果: GitHub の「Security → Code scanning alerts」に表示（既定ではアーティファクトとしては出力されません）
- ローカルクイックスタート
  - `pnpm -s security:scan` — ローカルでセキュリティスキャンを実行
  - `pnpm -s security:config` — 現在のセキュリティ設定を表示
 - 閾値はリポジトリ変数で制御できます（Settings → Variables → Repository variables に設定）。
  - `SECURITY_MAX_HIGH`（既定 0）: High 以上の許容数
  - `SECURITY_MAX_MODERATE`（既定 2）: Moderate の許容数
- 対象ワークフロー: `.github/workflows/sbom-generation.yml` で SBOM 生成・依存監査・CodeQL を実施し、必要に応じて上記閾値でエンフォースします。関連: `.github/workflows/security.yml`。
  - ブランチ保護: `main` で強制する場合は Settings → Branches → main → Require status checks に必要なセキュリティチェックを追加
  - スケジュール: 毎日 02:00 UTC にセキュリティスキャンを実施（`security.yml` の `schedule` を参照）

PRコメント例（`run-security` 時は非ブロッキング）

```
Security Summary
High/Critical: 0（許容: SECURITY_MAX_HIGH=0）
Moderate: 1（許容: SECURITY_MAX_MODERATE=2）
Policy: report-only（`enforce-security` を付与するとゲート）
Links: .github/workflows/sbom-generation.yml, docs/ci-policy.md
```

参考
- CIポリシー（ラベル/パス制御・Verify Lite 既定）: `docs/ci-policy.md`
- スラッシュコマンド対応表: `.github/workflows/agent-commands.yml`
