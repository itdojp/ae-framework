# Replay Mapping Example (scripts/testing/replay-runner.mjs)

This note shows a minimal way to prepare inputs and inspect outputs when using the replay runner.

- Input events (sample): `scripts/testing/fixtures/replay-sample.json`
- Failure sample (output-like): `scripts/testing/fixtures/replay-failure.sample.json`
- Missing traceId sample: `scripts/testing/fixtures/replay-missing-traceid.sample.json`（traceId 欠損ケースの挙動を確認）
- Failure (alt shape): `scripts/testing/fixtures/replay-failure.alt.sample.json`（violatedInvariants を byType 風に集約した例）
- Failure (alt2 shape): `scripts/testing/fixtures/replay-failure.bytype.alt2.sample.json`（byType 風の別例）
- Failure (alt3 byType): `scripts/testing/fixtures/replay-failure.bytype.alt3.sample.json`（byType 風、count/indices 併記）
- Failure (alt4 byType): `scripts/testing/fixtures/replay-failure.bytype.alt4.sample.json`（byType 風、割当過多の簡易例）
- Failure (alt5 byType): `scripts/testing/fixtures/replay-failure.bytype.alt5.sample.json`（byType 風、最小構成の割当過多）
- Failure (alt6 byType): `scripts/testing/fixtures/replay-failure.bytype.alt6.sample.json`（byType 風、さらに最小の2イベントケース）
- Failure (alt7 byType): `scripts/testing/fixtures/replay-failure.bytype.alt7.sample.json`（byType 風、単一タイプの複数違反をまとめた例）
- Failure (alt8 byType): `scripts/testing/fixtures/replay-failure.bytype.alt8.sample.json`（byType 風、onhand_min のみの連続違反）
- Failure (alt9 byType): `scripts/testing/fixtures/replay-failure.bytype.alt9.sample.json`（byType 風、onhand_min と allocated_le_onhand の混在）
- Failure (alt10 byType): `scripts/testing/fixtures/replay-failure.bytype.alt10.sample.json`（byType 風、allocated_le_onhand の連続違反＋one ok）
- Failure (alt11 byType): `scripts/testing/fixtures/replay-failure.bytype.alt11.sample.json`（byType 風、onhand_min=2 の閾値超過の組合せ）
- Failure (alt12 byType): `scripts/testing/fixtures/replay-failure.bytype.alt12.sample.json`（byType 風、allocated_le_onhand と onhand_min の交互違反）
- Failure (alt13 byType): `scripts/testing/fixtures/replay-failure.bytype.alt13.sample.json`（byType 風、onhand_min=1/2 混在＋allocated境界の複合）
- Failure (alt14 byType): `scripts/testing/fixtures/replay-failure.bytype.alt14.sample.json`（byType 風、連続OK→複合違反→OK の混在）
- Failure (alt15 byType): `scripts/testing/fixtures/replay-failure.bytype.alt15.sample.json`（byType 風、最小長の交互違反: onhand_min→allocated→onhand_min）
- Failure (alt16 byType): `scripts/testing/fixtures/replay-failure.bytype.alt16.sample.json`（byType 風、短系列で onhand_min と allocated の各1件）
- Failure (alt17 byType): `scripts/testing/fixtures/replay-failure.bytype.alt17.sample.json`（byType 風、onhand_min の複数違反が短系列で発生）
- Failure (alt18 byType): `scripts/testing/fixtures/replay-failure.bytype.alt18.sample.json`（byType 風、allocated_le_onhand の複数違反）
- Failure (alt19 byType): `scripts/testing/fixtures/replay-failure.bytype.alt19.sample.json`（byType 風、onhand_min と allocated_le_onhand の混在）
- Failure (alt20 byType): `scripts/testing/fixtures/replay-failure.bytype.alt20.sample.json`（byType 風、allocated と onhand_min の混在・短系列）
- Failure (alt21 byType): `scripts/testing/fixtures/replay-failure.bytype.alt21.sample.json`（byType 風、allocated と onhand_min の混在・複数違反）
- Failure (alt22 byType): `scripts/testing/fixtures/replay-failure.bytype.alt22.sample.json`（byType 風、allocated/onhand_min の混在・別順序）
- Failure (alt23 byType): `scripts/testing/fixtures/replay-failure.bytype.alt23.sample.json`（byType 風、onhand_min と allocated の混在・別順序）
- Failure (alt24 byType): `scripts/testing/fixtures/replay-failure.bytype.alt24.sample.json`（byType 風、onhand_min の複数違反・短系列）
- Failure (sample3): `scripts/testing/fixtures/replay-failure.sample3.json`（典型的な allocated_le_onhand / onhand_min の違反例）

Quick run
```
REPLAY_INPUT=scripts/testing/fixtures/replay-sample.json \
REPLAY_OUTPUT=artifacts/domain/replay.summary.json \
REPLAY_STRICT=0 pnpm tsx scripts/testing/replay-runner.mjs
```

Checks mapping (concept)
- allocated_le_onhand: allocated must not exceed onHand at any time
- onhand_min: onHand must be >= REPLAY_ONHAND_MIN (default 0)

A minimal failure example is provided at `scripts/testing/fixtures/replay-failure.sample.json` to illustrate `violatedInvariants` shape.
