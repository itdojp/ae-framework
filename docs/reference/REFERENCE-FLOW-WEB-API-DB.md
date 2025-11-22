# リファレンスフロー #1: Web API + DB (Agentic SDLC)

## 目的
- Web API + RDB/kv ストアを対象に、**エージェント協調型 SDLC** を「使える形」で提示するリファレンスフロー。
- GPT-5.1 Codex / Antigravity / Copilot など、IDE・モデル非依存で同じ型の成果物と検証パスに載せることを目的とする。

## 前提・設計方針
- コーディングは各種エージェント／IDE に委譲し、ae-framework は **仕様・検証・CI オーケストレーション** に集中する。
- 生成物は **JSON／markdown** を優先し、AJV/スキーマでエージェント生成物を検証する。
- 重テスト（mutation/MBT/property）はキャッシュ・スナップショット運用で再現性を確保し、`heavy-test-trends` アーティファクトで差分を確認する。

## 推奨リポジトリ構成（最小セット）
- `spec/bdd/` … Gherkin など例示仕様。`*.feature` + `steps/*.ts`
- `spec/properties/` … property-based 条件とジェネレータ
- `spec/api/` … OpenAPI/JSON Schema，下流で AJV 検証
- `tests/unit/`, `tests/integration/`, `tests/property/`
- `src/` … アプリ実装（例: Fastify/Express or NestJS）
- `docs/` … 運用・手順書（人間のみ / エージェント併用の 2 パスを記述）
- `plans/` … ExecPlan (Codex CLI 前提) のエントリポイント
- `.github/workflows/` … PR verify / nightly heavy / alert 用

## CI/検証パス（骨子）
- PR verify（既存の verify ワークフローを流用）
  - lint / type-check / unit / integration / property
  - mutation quick（`STRYKER_TIME_LIMIT=0`）※重い場合はオプション化
- Nightly heavy
  - mutation full + MBT + property 長時間
  - `scripts/pipelines/sync-test-results.mjs --store/--snapshot`
  - `scripts/pipelines/compare-test-trends.mjs --json-output reports/heavy-test-trends.json`
  - Slack/issue アラートは既存 heavy-test-alerts を流用

## ExecPlan（Codex CLI 想定の入口案）
1. `plans/web-api/01-spec.md` … 要件→API/BFF 境界→BDD/Property 草案を生成
2. `plans/web-api/02-tests.md` … Unit/Integration/Property スケルトン生成と TODO 挿入
3. `plans/web-api/03-impl.md` … 実装スキャフォールド（ORM/DB マイグレーション含む）
4. `plans/web-api/04-verify.md` … 必須検証（lint/type/unit/property）+ オプション（mutation quick）
5. `plans/web-api/05-pr.md` … PR 要約・リリースノート雛形

※ Antigravity/Gemini 等への横展開は、同じ計画を別エージェントでも踏めるよう JSON/Markdown I/O を維持する。

## 手順書の二経路
- **人間のみで回す場合**: `docs/flows/web-api-manual.md` を用意し、Spec→Test→Code→Verify→PR の手順とコマンド列を記述。
- **エージェント併用の場合**: `docs/flows/web-api-agent.md` を用意し、ExecPlan 実行手順、成果物検証（AJV/CI）、レビューガイドを記述。

## 初期タスク（このフローを「使える」状態にするための ToDo）
1. `plans/web-api/` 配下に上記 5 本の ExecPlan テンプレを追加（Codex CLI 用）
2. `docs/flows/web-api-manual.md` / `docs/flows/web-api-agent.md` を作成
3. `.github/` に Web API 前提の CI サンプル（lint/type/unit/integration/property + optional mutation quick）を追加
4. `spec/bdd/` と `spec/properties/` に最小サンプル（CRUD 1 テーブル想定）を配置
5. Issue/PR テンプレを Web API 前提で用意（acceptance criteria / spec links / test types）

## 参照
- 重テストキャッシュ/トレンド: `docs/ci/heavy-test-trend-archive.md`, `docs/ci/heavy-test-alerts.md`, `scripts/pipelines/sync-test-results.mjs`, `scripts/pipelines/compare-test-trends.mjs`
- CI 方針・ゲート: `docs/ci/phase2-ci-hardening-outline.md`, `docs/ci/label-gating.md`
- ポジショニング: `README.md`（Agentic SDLC Orchestrator & Spec/Verification Kit）
