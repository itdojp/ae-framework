# ajv Validation Failures: Examples & Messaging (#408)

> 🌍 Language / 言語: English | 日本語

---

## 日本語（概要）

よくある ajv 検証エラーの例と、エラーメッセージ方針（ファイルパス/キー/traceId を含め簡潔に、スキーマへの修正リンクを示す）をまとめています。

Examples
- Missing required `adapter`:
```
error: data must have required property 'adapter' at artifacts/jest/summary.json
```
- Invalid `status`:
```
error: data.status must be equal to one of the allowed values (ok|warn|error)
```
- Property summary missing `seed`:
```
error: data must have required property 'seed' at artifacts/properties/summary.json
```

Messaging Policy
- Show file path and offending key; include `traceId` if present.
- Fail fast; aggregate multiple errors but keep output concise.
- Suggest fix links to schema paths under `docs/schemas/`.
