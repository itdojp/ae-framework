# BDD Lint Usage (scripts/bdd/lint.mjs)

Run
```bash
npm run bdd:lint
```

Output (artifacts/bdd/lint.summary.json)
```json
{
  "violations": [
    { "file": "features/inventory.feature", "line": 12, "message": "When must use Aggregate Root command and avoid direct state mutation", "text": "When onHand is set to -1" }
  ]
}
```
