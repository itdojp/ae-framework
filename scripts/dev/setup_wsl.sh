#!/usr/bin/env bash
set -euxo pipefail

# 基本ツール
sudo apt-get update
sudo apt-get install -y curl jq git make python3-pip

# Podman（rootless）
sudo apt-get install -y podman podman-compose
mkdir -p $HOME/.config/containers

# Node.js（asdf 省略時）
curl -fsSL https://deb.nodesource.com/setup_22.x | sudo -E bash -
sudo apt-get install -y nodejs

# Apalache (TLA+) はコンテナ実行を推奨（Makefile から）
echo "WSL setup completed"