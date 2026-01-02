# Agent Builder フロー（最小実行）

## 目的
- #1047 の Agent Builder 連携に向けた最小フロー定義と実行方法のメモ。
- 仕様（Flow JSON）→ 実行（flow-runner）→ 検証結果（envelope）までの通し方を確認する。

## 主要ファイル
- Flow スキーマ: `schema/flow.schema.json`
- Flow サンプル: `fixtures/flow/sample.flow.json`
- 実行スクリプト: `scripts/agent-builder/flow-runner.mjs`
- 相関情報: `correlation.runId`（必須）/`commit`/`branch`（任意。監査/再現性の手がかり）

## 使い方（最小）
```bash
node scripts/agent-builder/flow-runner.mjs --flow fixtures/flow/sample.flow.json
```

### Agent Builder 形式のJSONを取り込む場合
```bash
node scripts/agent-builder/flow-runner.mjs \
  --flow /path/to/agent-builder.json \
  --adapter agent-builder
```

アダプタは以下の最小変換を行います。
- `id`/`name`/`key` → `id`（左から順に優先）
- `kind`/`type`/`action`/`role` → `kind`（左から順に優先）
- `parameters`/`config` → `params`
- `inputs`/`outputs` → `input`/`output`
- `source`/`target` → `from`/`to`

### verify-lite サマリを使う場合（任意）
```bash
node scripts/agent-builder/flow-runner.mjs \
  --flow fixtures/flow/sample.flow.json \
  --summary /path/to/verify-lite-summary.json \
  --output artifacts/agent-builder/envelope.json
```

## 出力
- 標準出力にノード実行サマリ（nodeId/kind/info）が出力される。
- `--summary` を指定した場合は Envelope JSON が生成され、`--output` を併用するとファイルに出力される。

## 備考
- `--help` でオプション一覧を表示できる。
- Flow/Envelope は `scripts/ci/validate-json.mjs` でスキーマ検証される。
