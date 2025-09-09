## Traceability Guide: Linking Feature Scenarios → Tests/Implementation/Formal Specs

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
- PR summary shows total scenarios and how many link to tests/impl/formal.
- The summary lists up to 5 unlinked scenarios for quick action.

### 6) Tips

- Keep references short and consistent. One line per major artifact is enough.
- Use tags for grouping; use slug for exact mapping across languages.
- Avoid overlinking: put references in the most representative file per flow.

