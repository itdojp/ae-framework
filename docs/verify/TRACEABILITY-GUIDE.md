## Traceability Guide: Linking Feature Scenarios → Tests/Implementation/Formal Specs

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

このガイドは、BDD シナリオ（.feature）と テスト／実装／形式仕様（TLA+/Alloy）を軽量な規約で関連付け、CI でトレーサビリティ行列（CSV/JSON）を生成する方法を説明します。

- シナリオに安定 ID（タグ/スラグ）を付与
- テスト/実装/形式仕様に一行参照コメントを追加
- CI が参照を集約し、カバレッジや未リンク項目、クリック可能な例を PR に要約

詳細は以下の英語セクションに従ってください。

This guide explains a lightweight convention to improve traceability across:

- BDD Scenarios (.feature)
- Tests (unit/integration)
- Implementation (src/*)
- Formal specs (TLA+ .tla / Alloy .als)

The CI builds a traceability matrix (CSV + JSON) and posts a PR summary.

### 1) Stable IDs and Tags in .feature

Use either tags or a stable ID slug to give each Scenario a durable handle.

```gherkin
@checkout @happy
Scenario: Checkout succeeds with in-stock items
  Given cart has 3 in-stock items
  When user pays with a valid card
  Then the order is created and inventory is reduced
```

Recommendations:
- Tags: start with feature-area and intent (e.g., `@checkout @happy`).
- Slug ID (optional): use scenario title as a slug in downstream references (the CI builder already derives `id = slug(title)`).

### 2) Tests: reference Scenario by name/id/tags

In test files, add a short reference comment or string literal that includes the scenario title, slug, or tags.

```ts
// Scenario: checkout-succeeds-with-in-stock-items @checkout @happy
describe('Checkout', () => {
  it('checkout succeeds with in-stock items', async () => {
    // ...
  });
});
```

Any of the following will link in CI:
- `Scenario: <exact title>` string
- The slug form (lowercase, non-alnum→`-`)
- A tag present at the scenario line (e.g., `@checkout`)

### 3) Implementation: minimal non-intrusive hints

Add a single-line reference near the main entry points for the feature flow.

```ts
// Scenario: checkout-succeeds-with-in-stock-items @checkout
export async function placeOrder(input: PlaceOrderInput) {
  // ...
}
```

For UI components, prefer referencing the scenario in Storybook stories or Playwright tests.

### 4) Formal Specs: cross-reference key scenarios

For TLA+ or Alloy, add a comment with the scenario slug or tag near the relevant property/predicate.

TLA+ example:
```tla
\* Scenario: checkout-succeeds-with-in-stock-items @checkout
THEOREM NoNegativeInventory == [] (Inventory >= 0)
```

Alloy example:
```alloy
// Scenario: checkout-succeeds-with-in-stock-items @checkout
assert NoNegativeInventory { all it: Item | it.stock >= 0 }
```

### 5) CI behavior

- The builder scans `.feature` files, extracts Scenario title, tags, and derives an `id` slug.
- It searches tests/src/formal for any occurrence of title/id/tag and generates:
  - `traceability.csv` for human eyeballing
  - `traceability.json` with totals and per-scenario rows
- PR summary includes:
  - Scenario totals and coverage percentages (tests/impl/formal)
  - Up to 5 unlinked scenarios (fast follow-up list)
  - Clickable examples (up to 3) with GitHub blob links built from the PR head SHA
  - Shortened path labels for readability (last two segments, e.g. `routes/checkout.ts`)
  - Hit-basis counts showing what matched each link (title/id/tag) for tests and formal

### 6) Tips

- Keep references short and consistent. One line per major artifact is enough.
- Use tags for grouping; use slug for exact mapping across languages.
- Avoid overlinking: put references in the most representative file per flow.
