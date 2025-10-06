# AWS OIDC Integration for Trace Payloads

Issue refs: #1036 / #1038 / #1011

## 概要
GitHub Actions から S3 バケットへ OTLP payload をアップロードする際、GitHub OIDC を用いることで長期のアクセストークンを不要にする構成をまとめる。

## IAM ロール設定
1. `ae-trace-collector` ロールを作成し、以下の信頼ポリシーを設定する。
   ```json
   {
     "Version": "2012-10-17",
     "Statement": [
       {
         "Effect": "Allow",
         "Principal": {
           "Federated": "arn:aws:iam::<account-id>:oidc-provider/token.actions.githubusercontent.com"
         },
         "Action": "sts:AssumeRoleWithWebIdentity",
         "Condition": {
           "StringEquals": {
             "token.actions.githubusercontent.com:aud": "sts.amazonaws.com"
           },
           "StringLike": {
             "token.actions.githubusercontent.com:sub": "repo:itdojp/ae-framework:*"
           }
         }
       }
     ]
   }
   ```
2. 権限ポリシー例。
   ```json
   {
     "Version": "2012-10-17",
     "Statement": [
       {
         "Effect": "Allow",
         "Action": ["s3:PutObject", "s3:GetObject", "s3:DeleteObject"],
         "Resource": "arn:aws:s3:::ae-trace-payloads/*"
       },
       {
         "Effect": "Allow",
         "Action": "s3:ListBucket",
         "Resource": "arn:aws:s3:::ae-trace-payloads"
       }
     ]
   }
   ```
3. バケット `ae-trace-payloads` を作成し、Lifecycle (30 日) やバージョニング設定は別途検討する。

## GitHub Actions 側の設定
- シークレット `AWS_TRACE_ROLE`: `arn:aws:iam::<account-id>:role/ae-trace-collector`
- 変数 `AWS_REGION`: 例 `ap-northeast-1`

```yaml
- name: Configure AWS credentials for trace payload
  uses: aws-actions/configure-aws-credentials@v4
  with:
    role-to-assume: ${{ secrets.AWS_TRACE_ROLE }}
    aws-region: ${{ vars.AWS_REGION }}

- name: Upload OTLP payload to S3
  run: |
    set -euo pipefail
    KEY="kvonce/${{ github.run_id }}/kvonce-otlp.json"
    aws s3 cp hermetic-reports/trace/collected-kvonce-otlp.json \
      "s3://ae-trace-payloads/${KEY}"
    PRESIGNED=$(aws s3 presign "s3://ae-trace-payloads/${KEY}" --expires-in 3600)
    echo "KVONCE_OTLP_S3_URI=s3://ae-trace-payloads/${KEY}" >> "$GITHUB_ENV"
    echo "KVONCE_OTLP_PAYLOAD_URL=$PRESIGNED" >> "$GITHUB_ENV"
    echo "KVONCE_OTLP_S3_REGION=${{ vars.AWS_REGION }}" >> "$GITHUB_ENV"
```

## fallback とローカル検証
- presigned URL が生成できない場合は `actions/upload-artifact` の出力を `KVONCE_OTLP_ARTIFACT_DIR` に設定し、従来どおり `--artifact-dir` 経路で取得可能。
- ローカルでは `scripts/trace/run-minio-poc.sh` を利用することで MinIO + 固定キーの環境を立ち上げ、`KVONCE_OTLP_S3_URI` フローを再現できる。

## TODO
- [ ] ライフサイクル (30 日) をバケットポリシーとして定義。
- [ ] presigned URL 失敗時の自動フォールバックをワークフローに追加。
- [ ] 夜間クリーンアップ（古いオブジェクトの削除）を検討。
