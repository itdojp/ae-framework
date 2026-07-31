---
docRole: ssot
lastVerified: '2026-07-31'
owner: infra-ops
verificationCommand: pnpm -s run check:doc-consistency
---

# Podman ベースのコンテナランタイム手順

AE-Framework のフルパイプラインは Podman を第一候補として設計されています。ここではローカル開発者が rootless Podman を使ってコンテナ依存タスク（Pact、API fuzz、Mutation Quick など）を再現するための前提条件と実行手順をまとめます。

## 前提条件

- Podman 4.8 以降（rootless モード）
- `podman-plugins` 1.7 以降（`podman compose` を提供。CI の Podman smoke では 1.7 未満で失敗します）
- `podman-compose` もしくは Podman ネイティブの Compose (`podman compose`) が利用可能であること
- `PODMAN_COMPOSE_PROVIDER` として `podman` または `podman-compose` を切り替えられるシェル環境
- Linux もしくは WSL2 上の Node.js 20（`pnpm` 10 系）

> Docker Desktop を利用していた従来の手順は互換層として残っていますが、CI とローカルの期待値を揃えるため Podman への切り替えを推奨します。

## Podman の起動確認

### インストール手順例 (Ubuntu 24.04)

```bash no-doctest
sudo apt-get update
sudo apt-get install -y podman podman-plugins
# 旧実装を併用する場合のみ
sudo apt-get install -y podman-compose
```

インストール後は以下のコマンドでネイティブ compose が利用可能かを確認してください。

```bash no-doctest
podman compose version
podman compose --help | head -n 20
```

出力されたバージョンが `1.7` 以上でない場合は `podman-plugins` のアップグレードを行ってください。

```bash no-doctest
# バージョン確認
podman info

# rootless systemd を使っている場合はユーザーサービスの起動状況も確認
loginctl show-user "$USER" -p Linger
systemctl --user status podman.socket
```

エラーが出る場合は `podman system migrate` を実行して設定を最新化してください。WSL2 では `sudo loginctl enable-linger $USER` を一度実行すると rootless サービスが安定します。

## Compose の切り替え

> Ubuntu 24.04 LTS では `sudo apt-get install podman podman-plugins` を実行するとネイティブ `podman compose` が導入されます。
> 最新の Podman Compose を利用できない場合は `podman-plugins` パッケージをアップグレードしてください。

```bash no-doctest
# Compose のバージョン確認
podman compose version
podman compose --help | head -n 20
```

パイプラインスクリプトは `PODMAN_COMPOSE_PROVIDER` 環境変数で Compose 実装を切り替えます。

```bash no-doctest
# Podman ネイティブ compose を優先
export PODMAN_COMPOSE_PROVIDER=podman

# 旧 podman-compose (Python 実装) にフォールバックする場合
export PODMAN_COMPOSE_PROVIDER=podman-compose
```

`podman compose` が未実装のディストリビューションでは自動的に `podman-compose` に切り替わります。Windows + WSL2 で Docker Desktop を併用する場合は、`PATH` から `/mnt/c/Program Files/Docker` を一時的に除外して Podman バイナリが選ばれるようにしてください。

## 主要タスクの実行例

```bash no-doctest
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

GitHub Actions でも同じ Podman ベースのパイプラインが動作します。ローカルで `pnpm pipelines:full` を実行して Verify Lite／Pact／API fuzz／Mutation Quick がすべて緑化することを確認してから PR を作成してください。Podman で取得したレポート (`reports/`, `artifacts/hermetic-reports/`) はそのまま CI の成果物構成と一致します。

### GitHub-hosted Container Security runtime

`Security Analysis` の `Container Security` job は、GitHub-hosted Ubuntu image が提供する reviewed container-tool bundleを使用します。job内で `apt-get install podman` を重ねると、runner bundleのPodman／conmon／OCI runtimeとUbuntu packageの旧tupleが混在するため、実行直前のpackage追加は行いません。

jobは `scripts/ci/container-runtime-preflight.mjs` を通して次をfail closedで確認します。

- runner image／kernel／architectureと、`apt-cache policy`によるPodman／Buildah／conmon／crun／runc inventory
- system path配下のregular executableと、parse可能なversion
- OCI runtime `features`応答
- digest-pinned minimal imageによる`podman run --rm`とminimal Containerfile `RUN true`
- explicit runtimeを適用した`podman info --debug`のeffective runtime
- repository image build、non-root `nextjs` user、archive export、Trivy scan、SARIF validation／upload

既定runtimeはrunner bundleの`runc`です。`/usr/local/bin/runc`を優先し、存在・version・direct smoke・minimal run/build・Podman effective runtimeがすべて一致した場合だけrepository buildへ進みます。runtimeの自動fallbackや、build／scan／SARIF failureのwarning変換は行いません。

bounded evidenceは`artifacts/container-security/container-runtime-diagnostic.json`へ`container-runtime-diagnostic/v1`として生成されます。`graphRoot`のprivate absolute pathやenvironment全量は保存せず、user/system storageの分類だけを保持します。classificationは`runtime-missing`、`runtime-version-incompatible`、`runtime-selection-invalid`、各build/export/scan/SARIF failureなどのclosed vocabularyです。check resultは`pass`／`fail`／`not-run`ごとにexit code、duration、detail、classificationの組み合わせを閉じ、timeout、malformed output、missing outputを別failureとして保持します。runtime candidateも同じstatus semanticsを使用し、unavailable candidateや未実行candidateをpassへ変換しません。

preflightの成功時点では`pipelineComplete=false`です。`manifest-detect -> repository-build -> image-user -> archive-export -> trivy-pull -> trivy-scan -> sarif-validate -> sarif-upload`の順に前提を検査し、12個すべてのreview済みcheckが一意にpassした後、`finalize`コマンドだけが`pipelineComplete=true`へ更新します。したがってruntime-readyな中間reportやfailure reportは診断用途には使用できますが、complete Container Security Evidenceとしては扱いません。

archive、SARIF、diagnostic reportのread boundaryはrepository-relative pathだけを受け取り、`.`／`..`／backslash／absolute pathと、finalを含む全path componentのsymlinkを拒否します。これはread前のbounded validationであり、同時filesystem mutationに対するatomic openを主張しません。structured artifactはread前にsizeを検査し、diagnostic JSONは256 KiB、Trivy SARIFは16 MiBを上限とします。上限超過時はtruncateせずfail closedです。上限変更は実際のartifact size evidence、memory bound、workflow timeoutを同じreviewで確認してください。

新規に制御するminimal smoke imageとTrivy imageはtagとdigestを併記します。更新時は、upstream release／registry digestを確認したreview済みPRでworkflow、fixture、runbookを同時更新し、同一exact headの独立した`workflow_dispatch`を2回成功させてください。repositoryの`node:22-alpine` base imageは今回のruntime selection contractとは別管理であり、無関係な大量pin変更は行いません。

`workflow_dispatch`の`mode=container-security`は、Container Security runtime pathだけを再現するfocused diagnosticです。実行時は`expected_head`へ40桁のcommit SHAを渡し、`github.sha`との完全一致をgateで検証します。通常の`push`／`schedule`では選択できず、Container Securityをsilent skipしません。focused runの成功はbuild／export／Trivy／SARIF pathのEvidenceであり、Dependency Audit、CodeQL、SBOMを含むfull Security Analysis成功へ昇格しません。full security acceptanceには`mode=all`または通常trusted eventの各lane成功が別途必要です。

### CI 共有ランナー向け手順

長時間の共有runnerやself-hosted laneでPodmanを利用する場合は、rootless Podmanを有効にした専用ランナーを用意します。パッケージの導入、`loginctl enable-linger`、`podman.socket` の常駐化など詳細な手順は以下を参照してください。GitHub-hosted `Container Security` jobは前節のbounded preflightを使用し、このself-hosted setupを暗黙の前提にしません。

- [Podman 共有ランナー構築ガイド](./podman-shared-runner.md)
