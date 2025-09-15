# Alloy 6 Specs (skeleton)

> 🌍 Language / 言語: English | 日本語

- Place Alloy 6 models here (e.g., `Domain.als`).
- Use LTL/past operators for temporal properties when applicable.

Example skeleton (Domain.als):

```
module Domain

sig State {}

pred Init[s: State] {}

pred Next[s, s': State] {}

assert Safety { all s: State | some s }

check Safety for 5
```

- With Alloy 6, enable temporal extension to check LTL/past.

---

## 日本語（概要）

このフォルダには Alloy 6 のモデル（例: `Domain.als`）を配置します。必要に応じて時相拡張（LTL / Past）を有効化し、時間的性質の検証を行ってください。

### スケルトン例（Domain.als）
```
module Domain

sig State {}

pred Init[s: State] {}

pred Next[s, s': State] {}

assert Safety { all s: State | some s }

check Safety for 5
```

### 注意
- LTL/Past を使う場合は Alloy 6 の時相拡張を有効化してください
- 小さいモデルから始め、段階的に制約を追加するとトラブルシュートが容易です
