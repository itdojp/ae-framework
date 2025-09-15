# TLA+ Specs (skeleton)

> 🌍 Language / 言語: English | 日本語

- Place TLA+ modules here (e.g., `DomainSpec.tla`).
- Start with safety invariants; add liveness as needed.
- Keep models small and composable; prefer assumptions per module.

Example skeleton (DomainSpec.tla):

```
------------------------------ MODULE DomainSpec ------------------------------
EXTENDS Naturals, Sequences

(* --algorithm sketch
variables state \in {"Init"}, history = <<>>;
end algorithm; *)

Init == TRUE
Next == UNCHANGED << >>

Invariant == TRUE

=============================================================================
```

- To verify with TLC: `tlc2 DomainSpec.tla` (if installed)
- To verify with Apalache: `apalache-mc check --inv=Invariant DomainSpec.tla`

---

## 日本語（概要）

このフォルダには TLA+ の仕様ファイル（例: `DomainSpec.tla`）を配置します。まずは安全性（safety）不変条件から始め、必要に応じて実行性（liveness）を追加してください。モデルは小さく合成しやすく保ち、モジュール単位で前提（assumption）を明示すると運用が容易になります。

### スケルトン例（DomainSpec.tla）
```
------------------------------ MODULE DomainSpec ------------------------------
EXTENDS Naturals, Sequences

(* --algorithm sketch
variables state \in {"Init"}, history = <<>>;
end algorithm; *)

Init == TRUE
Next == UNCHANGED << >>

Invariant == TRUE

=============================================================================
```

### 検証
- TLC を利用する場合: `tlc2 DomainSpec.tla`
- Apalache を利用する場合: `apalache-mc check --inv=Invariant DomainSpec.tla`
