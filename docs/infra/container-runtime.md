# Podman ベースのコンテナランタイム手順

AE-Framework のフルパイプラインは Podman を第一候補として設計されています。ここではローカル開発者が rootless Podman を使ってコンテナ依存タスク（Pact、API fuzz、Mutation Quick など）を再現するための前提条件と実行手順をまとめます。

## 前提条件

- Podman 4.8 以降（rootless モード）
- `podman-compose` もしくは Podman ネイティブの Compose (`podman compose`) が利用可能であること
- `PODMAN_COMPOSE_PROVIDER` として `podman` または `podman-compose` を切り替えられるシェル環境
- Linux もしくは WSL2 上の Node.js 20（`pnpm` 10 系）

> Docker Desktop を利用していた従来の手順は互換層として残っていますが、CI とローカルの期待値を揃えるため Podman への切り替えを推奨します。

## Podman の起動確認

```bash
# バージョン確認
podman info

# rootless systemd を使っている場合はユーザーサービスの起動状況も確認
loginctl show-user "$USER" -p Linger
systemctl --user status podman.socket
```

エラーが出る場合は `podman system migrate` を実行して設定を最新化してください。WSL2 では `sudo loginctl enable-linger $USER` を一度実行すると rootless サービスが安定します。

## Compose の切り替え

パイプラインスクリプトは `PODMAN_COMPOSE_PROVIDER` 環境変数で Compose 実装を切り替えます。

```bash
# Podman ネイティブ compose を優先
export PODMAN_COMPOSE_PROVIDER=podman

# 旧 podman-compose (Python 実装) にフォールバックする場合
export PODMAN_COMPOSE_PROVIDER=podman-compose
```

`podman compose` が未実装のディストリビューションでは自動的に `podman-compose` に切り替わります。Windows + WSL2 で Docker Desktop を併用する場合は、`PATH` から `/mnt/c/Program Files/Docker` を一時的に除外して Podman バイナリが選ばれるようにしてください。

## 主要タスクの実行例

```bash
# Verify Lite や Pact / API fuzz / Mutation quick を順次実行
pnpm pipelines:full

# Pact のみ実行
pnpm pipelines:pact

# API fuzz（Schemathesis）
pnpm pipelines:api-fuzz

# Mutation quick を Podman コンテナから実行
pnpm pipelines:mutation:quick
```

コンテナを利用するタスクは `reports/` や `temp-reports/` 以下に成果物を保存します。権限エラーが発生する場合はルートディレクトリに対してユーザー書き込み権限があるか確認してください。

## トラブルシューティング

| 症状 | 対処 |
|------|------|
| `could not connect to Podman socket` | `systemctl --user start podman.socket` を実行し、`podman info` で再度確認します。 |
| `Error: overlay: the backing xfs filesystem is formatted without d_type support` | `podman system migrate` を実行するか、WSL2 のディストリビューションを ext4 で再作成します。 |
| Compose 実行直後に「コンテナが存在しない」と警告が出る | 未起動サービスのクリーンアップ時に発生するため無害です。`PODMAN_COMPOSE_PROVIDER=podman-compose` に切り替えると抑制できる場合があります。 |
| WSL2 で Docker Desktop が優先される | `export PATH=$(printf '%s' "$PATH" | tr ':' '\n' | grep -v '^/mnt/c/' | paste -sd: )` で一時的に Docker バイナリを除外します。 |

## CI との整合性

GitHub Actions でも同じ Podman ベースのパイプラインが動作します。ローカルで `pnpm pipelines:full` を実行して Verify Lite／Pact／API fuzz／Mutation Quick がすべて緑化することを確認してから PR を作成してください。Podman で取得したレポート (`reports/`, `hermetic-reports/`) はそのまま CI の成果物構成と一致します。

### CI 共有ランナー向け手順

GitHub Actions 上で Podman を利用する場合は、rootless Podman を有効にした専用ランナーを用意する必要があります。パッケージの導入、`loginctl enable-linger`、`podman.socket` の常駐化など詳細な手順は以下を参照してください。

- [Podman 共有ランナー構築ガイド](./podman-shared-runner.md)


