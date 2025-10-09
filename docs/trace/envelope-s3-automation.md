# Envelope S3 Automation Plan

Issue refs: #1038 / #1042

## 目的
- Verify Lite / Trace pipeline で生成される Envelope を S3 にアップロードし、presigned URL を生成して Slack に通知する。
- CLI 化し、GitHub Actions とローカル環境の両方で再利用できるよう整備する。

## 要求仕様
1. `scripts/trace/upload-envelope.mjs` を利用して S3 にアップロードしたファイルに対して presigned URL を生成する。
2. presigned URL と GitHub Actions のメタデータを Slack Webhook に送信できる（dry-run では標準出力のみ）。
3. 生成したメタデータを JSON (`artifacts/trace/publish-envelope.json`) に保存し、後続の Step Summary や GitHub コメントで参照可能にする。
4. CLI は AWS 認証情報がない場合には早期にエラーを出し、dry-run で挙動を確認できる。

## CLI: `scripts/trace/publish-envelope.mjs`
```
Usage: node scripts/trace/publish-envelope.mjs [options]
  -e, --envelope <file>       Envelope JSON (default: artifacts/report-envelope.json)
  -b, --bucket <name>         S3 bucket (required)
  -k, --key <key>             S3 key (default: envelopes/<runId>/<filename>)
      --expires <seconds>     Presigned URL expiration (default: 604800)
      --slack-webhook <url>   Slack Incoming Webhook URL (optional)
      --slack-channel <name>  Slack channel label (optional)
      --output <file>         Metadata JSON path (default: artifacts/trace/publish-envelope.json)
      --dry-run               Upload/presign/slack を行わずプレビューのみ
      --help
```

## 実行フロー
1. Envelope JSON を読み込み、`correlation.runId` などを取り出す。
2. dry-run でなければ `upload-envelope.mjs` を呼び出し S3 へアップロード。
3. `aws s3 presign` で presigned URL を生成。
4. Slack Webhook が設定されている場合は通知文を組み立て送信（dry-run 時は標準出力にプレビュー）。
5. `artifacts/trace/publish-envelope.json` に実行結果（bucket/key/presignedUrl/dryRun 等）を書き出す。

## 後続 TODO
- GitHub Actions ワークフローから `publish-envelope.mjs` を呼び出し、Step Summary へ presigned URL を追記する。
- `post-envelope-comment.mjs` の `### Trace Domains` に加えて `### Presigned URL` を追加し、Slack 同等の情報をコメントにも展開する。
- 環境ごとに bucket/key を切り替えるための設定ファイル (`envelope.publish.config.json` など) を導入する。
