---
docRole: narrative
lastVerified: '2026-03-12'
---

# BDD Lint Usage (scripts/bdd/lint.mjs)

> 🌍 Language / 言語: English | 日本語

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
