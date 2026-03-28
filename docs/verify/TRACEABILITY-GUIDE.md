---
docRole: narrative
lastVerified: '2026-03-28'
---
# Traceability Guide: Linking Feature Scenarios -> Tests/Implementation/Formal Specs

> 🌍 Language / 言語: English | 日本語

---

## English

This guide explains a lightweight convention to improve traceability across:

- BDD scenarios (`.feature`)
- tests (unit / integration)
- implementation (`src/*`)
- formal specs (TLA+ `.tla` / Alloy `.als`)

The CI builds a traceability matrix (CSV + JSON) and posts a PR summary.

### 1) Stable IDs and tags in `.feature`

Use either tags or a stable ID slug to give each scenario a durable handle.

```text
@checkout @happy
Scenario: Checkout succeeds with in-stock items
  Given cart has 3 in-stock items
  When user pays with a valid card
  Then the order is created and inventory is reduced
```

Recommendations:
- Tags should start with a feature area and intent, for example `@checkout @happy`.
- Slug IDs are optional, because the CI builder already derives `id = slug(title)` from the scenario title.

### 2) Tests: reference the scenario by name / id / tags

In test files, add a short reference comment or string literal that includes the scenario title, slug, or tags.

```text
// Scenario: checkout-succeeds-with-in-stock-items @checkout @happy
describe('Checkout', () => {
  it('checkout succeeds with in-stock items', async () => {
    // ...
  });
});
```

Any of the following will link in CI:
- `Scenario: <exact title>`
- the slug form (`lowercase`, non-alnum -> `-`)
- a tag present on the scenario line, for example `@checkout`

### 3) Implementation: minimal non-intrusive hints

Add a single-line reference near the main entry points for the feature flow.

```text
// Scenario: checkout-succeeds-with-in-stock-items @checkout
export async function placeOrder(input: PlaceOrderInput) {
  // ...
}
```

For UI components, prefer referencing the scenario in Storybook stories or Playwright tests.

### 4) Formal specs: cross-reference key scenarios

For TLA+ or Alloy, add a comment with the scenario slug or tag near the relevant property or predicate.

TLA+ example:
```text
\* Scenario: checkout-succeeds-with-in-stock-items @checkout
THEOREM NoNegativeInventory == [] (Inventory >= 0)
```

Alloy example:
```text
// Scenario: checkout-succeeds-with-in-stock-items @checkout
assert NoNegativeInventory { all it: Item | it.stock >= 0 }
```

### 5) CI behavior

- The builder scans `.feature` files, extracts scenario titles and tags, and derives an `id` slug.
- It searches `tests/`, `src/`, and formal artifacts for any occurrence of the title, id, or tag and generates:
  - `traceability.csv` for human inspection
  - `traceability.json` with totals and per-scenario rows
- The PR summary includes:
  - scenario totals and coverage percentages (`tests` / `impl` / `formal`)
  - up to 5 unlinked scenarios for fast follow-up
  - up to 3 clickable examples with GitHub blob links built from the PR head SHA
  - shortened path labels for readability (for example `routes/checkout.ts`)
  - hit-basis counts showing what matched each link (`title` / `id` / `tag`) for tests and formal

### 6) Tips

- Keep references short and consistent. One line per major artifact is enough.
- Use tags for grouping, and use slugs for exact mapping across languages.
- Avoid overlinking. Put the reference in the most representative file for the flow.

## 日本語

このガイドは、以下の対象に対して軽量なトレーサビリティ規約を導入する方法を説明します。

- BDD シナリオ（`.feature`）
- テスト（unit / integration）
- 実装（`src/*`）
- 形式仕様（TLA+ `.tla` / Alloy `.als`）

CI はトレーサビリティ行列（CSV / JSON）を生成し、PR summary に要点を追記します。

### 1) `.feature` に安定 ID とタグを付ける

各シナリオに durable な識別子を与えるため、タグまたは安定した slug ID を使います。

```text
@checkout @happy
Scenario: Checkout succeeds with in-stock items
  Given cart has 3 in-stock items
  When user pays with a valid card
  Then the order is created and inventory is reduced
```

推奨:
- タグは feature area と intent から始めます。例: `@checkout @happy`
- slug ID は任意です。CI builder が scenario title から `id = slug(title)` を自動導出します。

### 2) テスト: scenario 名 / id / tag で参照する

テストファイルでは、scenario title、slug、または tag を含む短い参照コメントや string literal を追加します。

```text
// Scenario: checkout-succeeds-with-in-stock-items @checkout @happy
describe('Checkout', () => {
  it('checkout succeeds with in-stock items', async () => {
    // ...
  });
});
```

CI では、次のいずれでもリンクされます。
- `Scenario: <exact title>`
- slug form（`lowercase`、非英数字は `-`）
- scenario 行にある tag。例: `@checkout`

### 3) 実装: 非侵襲な最小ヒントを置く

feature flow の主要な entry point の近くに、一行だけ参照を置きます。

```text
// Scenario: checkout-succeeds-with-in-stock-items @checkout
export async function placeOrder(input: PlaceOrderInput) {
  // ...
}
```

UI component では、component 本体より Storybook story や Playwright test で参照する方を優先してください。

### 4) 形式仕様: 主要 scenario を相互参照する

TLA+ や Alloy では、関連する property / predicate の近くに scenario slug または tag を含むコメントを置きます。

TLA+ の例:
```text
\* Scenario: checkout-succeeds-with-in-stock-items @checkout
THEOREM NoNegativeInventory == [] (Inventory >= 0)
```

Alloy の例:
```text
// Scenario: checkout-succeeds-with-in-stock-items @checkout
assert NoNegativeInventory { all it: Item | it.stock >= 0 }
```

### 5) CI の挙動

- builder は `.feature` を走査し、scenario title と tag を抽出し、`id` slug を導出します。
- `tests/`、`src/`、formal artifact を検索し、title / id / tag の一致から次を生成します。
  - `traceability.csv`：人手確認用
  - `traceability.json`：total と per-scenario row を含む機械可読出力
- PR summary には次を含みます。
  - scenario total と coverage percentage（`tests` / `impl` / `formal`）
  - 最大 5 件の unlinked scenario
  - PR head SHA から構築した GitHub blob link 付きの clickable example を最大 3 件
  - 可読性のため短縮した path label（例: `routes/checkout.ts`）
  - tests / formal で何が一致したかを示す hit-basis count（`title` / `id` / `tag`）

### 6) 運用上の注意

- 参照は短く、一貫した形式で維持してください。主要 artifact ごとに一行で十分です。
- grouping には tag、厳密な対応付けには slug を使ってください。
- 過剰にリンクしないでください。flow を代表するファイルに参照を置くのが原則です。
