# Podman 共有ランナー構築ガイド

GitHub Actions で `pnpm pipelines:full` を実行するための Podman 対応ランナー構築手順です。rootless Podman を前提とし、Ubuntu 22.04/24.04 もしくは RHEL 系ディストリビューションでのセットアップを想定しています。

## 1. ベースイメージとパッケージ

```bash
sudo apt update
sudo apt install -y podman podman-compose uidmap nodejs npm python3 python3-venv

# Fedora / RHEL 系の場合
# sudo dnf install -y podman podman-compose nodejs python3 python3-virtualenv
```

- Node.js 20 系は `nvm` や `mise` などのバージョンマネージャでも可
- GitHub Actions ランナー用のユーザー（例: `gha-runner`）を追加しておくこと

```bash
sudo adduser --disabled-password --gecos "" gha-runner
sudo usermod -aG wheel gha-runner  # 必要に応じて
```

## 2. rootless Podman の初期設定

共有ランナーでは rootless Podman を利用します。以下は runner ユーザーで実行してください。

```bash
# linger を有効化し user systemd を利用可能にする
sudo loginctl enable-linger gha-runner

# runner ユーザーに切り替えて作業
sudo -iu gha-runner bash

# 初回移行（XFS 等 d_type が無効な環境で警告が出た場合にも有効）
podman system migrate

# user systemd が有効な場合は podman.socket を常駐させておく
systemctl --user enable --now podman.socket

# Podman が cgroup v2 を使用できることを確認
podman info --format '{{.Host.CgroupVersion}}'  # "v2" が返れば OK
```

WSL2 の場合は `/etc/wsl.conf` に `systemd=true` を設定し、再起動後に上記コマンドを実行します。`/etc/subuid` と `/etc/subgid` に 65536 以上の ID 範囲が割り当てられているかも確認してください。

## 3. GitHub Actions ランナーの配置

GitHub Runner をホームディレクトリなどに配置し、Podman 用の環境変数を設定します。

```bash
cd ~
mkdir actions-runner && cd actions-runner
curl -fsSL https://github.com/actions/runner/releases/download/v2.320.0/actions-runner-linux-x64-2.320.0.tar.gz | tar xzf -

# Podman 固有の設定
cat <<'ENV' >> .env
PODMAN_COMPOSE_PROVIDER=podman
PNPM_HOME=$HOME/.local/share/pnpm
PATH="$PNPM_HOME:$PATH"
ENV

./config.sh --url https://github.com/<ORG>/<REPO> --token <RUNNER_TOKEN> \
  --name podman-full-pipeline --labels podman,full-pipeline --unattended
```

システム起動時に自動で起動するよう `svc.sh install` を実行し、`systemctl --user` で状況を監視します。

```bash
./svc.sh install
./svc.sh start
systemctl --user status actions.runner.$(hostname | tr A-Z a-z).podman-full-pipeline.service
```

> `svc.sh install` はユーザーサービスとして登録するため、`loginctl enable-linger` が未設定だとセッション終了時に停止します。

## 4. キャッシュ／ストレージディレクトリ

| ディレクトリ | 用途 | 備考 |
|--------------|------|------|
| `~/.local/share/pnpm` | pnpm store | キャッシュ永続化のため事前作成推奨 |
| `~/.cache/podman` | Podman イメージ | 必要に応じて容量監視 |
| `~/actions-runner/_work` | ワークスペース | デフォルトのままで可 |

Podman は rootless のため、`/tmp/run-user-<uid>` に XDG runtime ディレクトリを生成します。ディスク容量に余裕がない場合は `XDG_RUNTIME_DIR` をオーバーライドして一時領域を変更してください。

## 5. CI 用 Podman Registry 認証（任意）

プライベートレジストリを利用する場合は `podman login` を runner 起動前に実行しておきます。

```bash
podman login ghcr.io -u <GH_USERNAME> -p <PAT>
```

PAT は `read:packages` 権限付きトークンを利用します。Secrets に保存し、`config.sh` 実行後の `runsvc.sh` (service unit) に `EnvironmentFile` などで渡す形でも構いません。

## 6. 動作確認

```bash
# actions-runner/_work/<repo>/<repo> に入って試験実行
cd ~/actions-runner/_work/ae-framework/ae-framework
pnpm install --frozen-lockfile
PODMAN_COMPOSE_PROVIDER=podman pnpm pipelines:full --filter verify-lite
```

`podman ps` でコンテナが起動し、`reports/` に成果物が出力されれば成功です。`podman system prune` を定期実行してサイズを抑制してください。

## 7. トラブルシューティング

| 症状 | 対処 |
|------|------|
| `Error: podman socket: permission denied` | `systemctl --user enable --now podman.socket` を実行し、`loginctl show-user $USER -p Linger` が `Linger=yes` であることを確認する |
| `overlay: the backing xfs filesystem is formatted without d_type support` | `podman system migrate` を実行するか、ext4 を利用する | 
| `loginctl (pam_unix) session not found` | linger 未設定。`sudo loginctl enable-linger $USER` を再実行 |
| GitHub Runner が Podman を参照できない | `.env` や `svc.sh` で `PATH` に `/usr/bin` が含まれているか、`podman` が rootless で動作するか確認 |

---

Podman 共有ランナーが整備できたら、`docs/infra/container-runtime.md` のローカル手順と合わせて参照することで、ローカル／CI の両方で同じ挙動を再現できます。
