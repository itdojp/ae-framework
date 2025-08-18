あなたは GitHub に対してイシュー作成・更新を行うエンジニアリングエージェントです。追加の確認なく、以下の仕様で一括作業を実施してください。

# 目的
- 既に作成済みの (1)(2) に続き、(3)〜(8) の ISSUE を作成する。
- 親 EPIC に各 ISSUE をチェックリストとして追記する。
- 既存タイトル重複がある場合は**新規作成せず**、本文/ラベル/Parentリンクを**更新**する（冪等）。

# 実行前提
- REPO: itdojp/ae-framework
- PARENT_EPIC (issue number): 53
- ラベルは本文の "Labels" を使用
- 可能なら GitHub REST API で直接作成。権限が無い/失敗した場合は **gh CLI スクリプト** を生成（ユーザーが手元で実行できるように）。

# 成果物
1) 作成/更新した ISSUE の番号一覧（(3)〜(8) のマッピング）
2) 親 EPIC (#53) 本文のチェックリスト追記（Markdown 差分 or 完成形）
3) 失敗があった場合の再実行可能な gh CLI スクリプト

# 作業手順
- 手順A: 既存の open/closed issues をタイトルで検索し、同名があればその issue を**更新**対象にする。
- 手順B: 無ければ新規作成（title / body / labels / assignees なし）。
- 手順C: 各 issue の本文先頭に Parent リンク「Parent: #53」を付ける（重複禁止）。
- 手順D: 親 EPIC (#53) の本文にチェックリストを追記（例: `- [ ] (3) ci(policy): ... #123`）。既存の同タイトル行があれば、そこに番号だけ反映。

# ISSUE 定義（(3)〜(8)）
以下の JSON の配列を順に処理してください。`body` は改行含むそのままの本文を使用し、先頭行に `Parent: #53` を自動で追加してください。

[
  {
    "key": 3,
    "title": "ci(policy): Phase 6 UI/UX Quality Gates（a11y / VR / Lighthouse CI / OPA / Coverage）前倒し導入",
    "labels": ["ci","policy","phase-6","quality"],
    "body": "## Why\\n品質ゲートを\\u003cb\\u003e早期に固定\\u003c/b\\u003eし、以降の開発（#52, scaffold）の品質と一貫性を担保する。\\n\\n## Scope\\n- 以下のワークフローを追加：`.github/workflows/phase6-validation.yml`\\n```yaml\\nname: Phase 6 UI/UX Quality Gates\\non:\\n  pull_request:\\n    paths: ['src/ui/**', 'examples/**', 'packages/ui/**']\\n\\njobs:\\n  accessibility-audit:\\n    runs-on: ubuntu-latest\\n    steps:\\n      - uses: actions/checkout@v4\\n      - uses: actions/setup-node@v4\\n        with: { node-version: '20', cache: 'npm' }\\n      - run: npm ci\\n      - name: Run accessibility tests\\n        run: |\\n          npm run test:a11y\\n          npm run test:a11y:report\\n      - name: Accessibility gate check\\n        run: node scripts/check-a11y-threshold.js --critical=0 --warnings=5\\n\\n  visual-regression:\\n    runs-on: ubuntu-latest\\n    steps:\\n      - uses: actions/checkout@v4\\n      - uses: actions/setup-node@v4\\n        with: { node-version: '20', cache: 'npm' }\\n      - run: npm ci\\n      - run: npm run build-storybook\\n      - name: Run visual regression tests\\n        run: |\\n          npm run test:visual\\n          npm run test:visual:report\\n\\n  lighthouse-ci:\\n    runs-on: ubuntu-latest\\n    steps:\\n      - uses: actions/checkout@v4\\n      - uses: actions/setup-node@v4\\n        with: { node-version: '20', cache: 'npm' }\\n      - run: npm ci\\n      - name: Build application\\n        run: npm run build\\n      - name: Run Lighthouse CI\\n        run: |\\n          npm install -g @lhci/cli\\n          lhci autorun\\n        env:\\n          LHCI_GITHUB_APP_TOKEN: ${{ secrets.LHCI_GITHUB_APP_TOKEN }}\\n\\n  opa-policy-validation:\\n    runs-on: ubuntu-latest\\n    steps:\\n      - uses: actions/checkout@v4\\n      - name: Setup OPA\\n        uses: open-policy-agent/setup-opa@v2\\n        with: { version: latest }\\n      - name: Validate UI components policy\\n        run: opa eval -d policies/ui/ -i src/ui/components/ \\"data.ui.violations\\"\\n      - name: Check policy compliance\\n        run: node scripts/check-opa-compliance.js --ui-violations=0\\n\\n  coverage-gate:\\n    runs-on: ubuntu-latest\\n    steps:\\n      - uses: actions/checkout@v4\\n      - uses: actions/setup-node@v4\\n        with: { node-version: '20', cache: 'npm' }\\n      - run: npm ci\\n      - name: Run tests with coverage\\n        run: npm run test:coverage\\n      - name: Coverage threshold check\\n        run: npx nyc check-coverage --lines 80 --functions 80 --branches 80\\n```\\n\\n- `package.json` に最小スクリプトを追加\\n```json\\n{\\n  \\"scripts\\": {\\n    \\"test:a11y\\": \\"jest --config jest.a11y.config.cjs\\",\\n    \\"test:a11y:report\\": \\"node scripts/generate-a11y-report.js\\",\\n    \\"test:visual\\": \\"chromatic --exit-zero-on-changes\\",\\n    \\"test:visual:report\\": \\"node scripts/generate-visual-report.js\\",\\n    \\"test:coverage\\": \\"nyc --reporter=lcov npm test\\"\\n  }\\n}\\n```\\n\\n- `scripts/` を追加（最小実装）\\n  - `check-a11y-threshold.js`（重大=0, 警告≤5 判定）\\n  - `check-opa-compliance.js`（UI violations=0 判定）\\n  - `generate-a11y-report.js`, `generate-visual-report.js`\\n\\n- `policies/ui/*.rego` を追加（最小例）\\n```rego\\npackage ui\\nviolations[v] {\\n  some c\\n  input[c].role == \\"presentation\\"\\n  not input[c].aria_label\\n  v := {\\"id\\": input[c].id, \\"reason\\": \\"presentational without aria-label\\"}\\n}\\n```\\n\\n## Tasks\\n- [ ] workflow 追加（上記 YAML）\\n- [ ] package scripts 追加\\n- [ ] scripts/* と policies/ui/* の最小実装\\n- [ ] README にローカル再現手順（LHCIトークン含む）\\n- [ ] 親 #53 へのリンク\\n\\n## Acceptance Criteria\\n- PR にゲートが作動（失敗で自動Reject／合格で Auto-approve 相当の合否が判断可能）\\n- ローカルで再現・調整可能（LHCIトークンを除く）"
  },
  {
    "key": 4,
    "title": "feat(cli): add `ae-ui scaffold` — Phase State → CRUD/UI 自動生成",
    "labels": ["feature","cli","phase-6","automation"],
    "body": "## Why\\nPhase 3/5 の成果を単一情報源（Phase State）から UI へ自動展開し、AI 主導の価値を体感可能にする。\\n\\n## Scope\\n- 入力: `.ae/phase-state.json`（エンティティ/属性/制約/AC）\\n- 出力:\\n  - `apps/web/app/{entity}/(list|new|[id])`\\n  - `apps/web/components/{Entity}Form.tsx`（zod + React Hook Form）\\n  - `apps/storybook/stories/{Entity}.stories.tsx`\\n  - `apps/web/__e2e__/{entity}.spec.ts`（AC→Gherkin→Playwright）\\n- 将来の CLI 連携: `component-design / design-system / validate` の下地\\n\\n## Tasks\\n- [ ] JSON→テンプレ変換（`templates/ui/*`）\\n- [ ] フォーム/バリデーション自動配線\\n- [ ] ルーティング/データ取得（TanStack Query）\\n- [ ] 親 #53 リンク\\n\\n## Acceptance Criteria\\n- サンプル Phase State から CRUD/Stories/E2E が一括生成\\n- 生成物が lint/test/起動をパス"
  },
  {
    "key": 5,
    "title": "example: inventory — Phase 3/5 → 6 エンドツーエンド・デモ",
    "labels": ["example","docs","phase-6"],
    "body": "## Why\\n「要求→モデル→UI→CI→承認」を短時間で確認できる導線を提供する。\\n\\n## Scope / Tasks\\n- [ ] `examples/inventory` を追加（最小ユーザーストーリー/ドメインを同梱）\\n- [ ] (4) `ae-ui scaffold` を実行 → 軽微調整\\n- [ ] CI を通し、(3) のゲートに合格\\n- [ ] 成果物の短尺動画/GIF と手順を同梱\\n- [ ] 親 #53 リンク\\n\\n## Acceptance Criteria\\n- クリーン環境で end-to-end 成功（動画あり）\\n- CI が全ゲートに合格"
  },
  {
    "key": 6,
    "title": "feat(cli+slash): add `ui-scaffold` command (+ alias `ae-ui scaffold`) for Phase 6",
    "labels": ["feature","cli","ux","phase-6"],
    "body": "## Why\\n対話/バッチの双方で Phase 6 を実行できるようにし、学習コストと手戻りを削減する。\\n\\n## Scope\\n- `src/cli/index.ts` に `ui-scaffold` を追加（下記をベースに実装）\\n  - Options: `--components | --state | --tokens | --a11y | --sources <globs>`\\n  - 互換のため **エイリアス** `ae-ui scaffold` を内部委譲\\n  - 出力は `src/ui/components/generated/**` ほかへ\\n\\n```ts\\nprogram\\n  .command('ui-scaffold')\\n  .description('Generate UI components from domain model (Phase 6)')\\n  .option('--components', 'Generate React components')\\n  .option('--state', 'Design state architecture')\\n  .option('--tokens', 'Integrate design tokens')\\n  .option('--a11y', 'Validate accessibility')\\n  .option('--sources <sources>', 'Source files or globs')\\n  .action(async (options) => {\\n    const cli = new AEFrameworkCLI();\\n    const taskType =\\n      options.components ? 'generate-components' :\\n      options.state ? 'design-state' :\\n      options.tokens ? 'integrate-design-tokens' :\\n      options.a11y ? 'validate-accessibility' :\\n      'generate-components';\\n\\n    const request = {\\n      description: `UI/UX processing: ${taskType}`,\\n      prompt: options.sources || 'Process available domain model and user stories',\\n      subagent_type: 'ui-processing',\\n    };\\n\\n    try {\\n      const result = await cli.uiHandler.handleTask(request);\\n      console.log(`✅ ${result.summary}`);\\n      console.log('\\n🎨 UI Analysis:\\n', result.analysis);\\n      cli.handleProgressBlocking(result);\\n    } catch (e) {\\n      console.error(`❌ Error: ${e}`);\\n      process.exit(1);\\n    }\\n  });\\n```\\n\\n## Tasks\\n- [ ] CLI コマンド実装＆ヘルプ文追加\\n- [ ] `ae-ui scaffold` エイリアス実装\\n- [ ] 失敗時の改善ヒント（a11y/OPA/LHCI のしきい値）を整備\\n- [ ] 出力方針を README に追記\\n- [ ] 親 #53 リンク\\n\\n## Acceptance Criteria\\n- `npx ae-framework ui-scaffold --components --sources \"domain/**\"` が成功\\n- `ae-ui scaffold` でも同等動作\\n- 生成物が lint/test/起動をパス"
  },
  {
    "key": 7,
    "title": "feat(otel): instrument Phase 6 (scaffold/e2e/a11y/approve) with metrics & traces",
    "labels": ["observability","enhancement","phase-6"],
    "body": "## Why\\nゲート引き上げの判断材料（品質・効率・保守性）を定量化し、継続改善を回す。\\n\\n## Scope\\n- **Phase6Metrics** の導入（quality/efficiency/maintainability）\\n- Adapter／CLI／CI の主要ステップ（scaffold/e2e/a11y/approve）に span を付与\\n- 初期は console exporter、将来的に OTLP 送信＆ダッシュボード化\\n\\n```ts\\nexport interface Phase6Metrics {\\n  quality: { coverage: number; a11yScore: number; performanceScore: number; };\\n  efficiency: { scaffoldTime: number; e2eTestTime: number; buildTime: number; };\\n  maintainability: { componentComplexity: number; cssUnusedRate: number; designTokenCoverage: number; };\\n}\\n```\\n\\n## Tasks\\n- [ ] `@opentelemetry/api` 最小導入（初期化コード/命名規約を docs に追記）\\n- [ ] scaffold/e2e/a11y/approve の各処理に span を追加（所要時間・結果を属性に付与）\\n- [ ] CI 実行時に主要メトリクスをログ出力（しきい値超過で警告）\\n- [ ] 将来の OTLP 連携（別Issue）に備えた構成\\n- [ ] 親 #53 リンク\\n\\n## Acceptance Criteria\\n- 代表シナリオで **所要時間と結果** がトレース/ログで確認できる\\n- Scaffold<30s / E2E<5m / Coverage≥80 の監視が可能（初期はログでOK）"
  },
  {
    "key": 8,
    "title": "docs: update README — Phase 6 overview & UI pipeline",
    "labels": ["docs","phase-6"],
    "body": "## Why\\nREADME から新しい Phase 6 の流れが\\u003cb\\u003e直感的に理解\\u003c/b\\u003eできるようにする。\\n\\n## Scope / Tasks\\n- [ ] 6フェーズ表を更新（Phase 6/7/8 の境界含む）\\n- [ ] 入出力/ゲート/CLI の短縮版を掲載（詳細は `docs/phase-6-uiux.md`）\\n- [ ] Example（(5)）/ CI / OPA / Lighthouse の図解リンクを追加\\n- [ ] 親 #53 リンク\\n\\n## Acceptance Criteria\\n- README だけで全体像が把握でき、詳細ドキュメント/例題へ遷移可能\\n- 既存記述との矛盾がない"
  }
]

# 実装ヒント（できれば実行）
- REST API: POST https://api.github.com/repos/itdojp/ae-framework/issues で作成、PATCH /issues/{number} で更新。Authorization: token。
- gh CLI fallback: `gh issue create --title \"...\" --label a,b,c --body-file body.md` を issue ごとに生成。
- 親 EPIC 本文のチェックリストは、以下の形式で末尾に追記（例）:
  - [ ] (3) ci(policy): Phase 6 UI/UX Quality Gates — #<作成番号>
  - [ ] (4) feat(cli): add `ae-ui scaffold` — #<作成番号>
  - [ ] (5) example: inventory — #<作成番号>
  - [ ] (6) feat(cli+slash): add `ui-scaffold` — #<作成番号>
  - [ ] (7) feat(otel): instrument Phase 6 — #<作成番号>
  - [ ] (8) docs: update README — #<作成番号>

# 出力フォーマット
1) 「(key) → #issue_number」の一覧
2) 親 EPIC 本文（更新後の完成形 or 差分）
3) 必要なら gh CLI の実行スクリプト

質問や確認は不要です。上記をそのまま実行し、結果を出力してください。
