#!/usr/bin/env bash
set -euo pipefail

LOCKFILE_PATH="${AE_LOCKFILE_PATH:-pnpm-lock.yaml}"
INSTALL_FLAGS="${AE_LOCKFILE_INSTALL_FLAGS:---no-frozen-lockfile --prefer-offline --ignore-scripts}"

if ! command -v pnpm >/dev/null 2>&1; then
  echo "::error::pnpm is required but was not found in PATH"
  exit 2
fi

if ! command -v git >/dev/null 2>&1; then
  echo "::error::git is required but was not found in PATH"
  exit 2
fi

if [ ! -f "$LOCKFILE_PATH" ]; then
  echo "::error::Lockfile not found: $LOCKFILE_PATH"
  exit 2
fi

echo "Lockfile reproducibility check"
echo "- lockfile: $LOCKFILE_PATH"
echo "- install flags: $INSTALL_FLAGS"

has_lockfile_changes() {
  git status --porcelain -- "$LOCKFILE_PATH" | grep -q .
}

if has_lockfile_changes; then
  echo "::error::Precondition failed: lockfile already has staged or unstaged changes"
  git --no-pager diff -- "$LOCKFILE_PATH" || true
  git --no-pager diff --cached -- "$LOCKFILE_PATH" || true
  exit 2
fi

pnpm install $INSTALL_FLAGS

if has_lockfile_changes; then
  echo "::error::Lockfile drift detected after pnpm install."
  echo "::error::Regenerate and commit $LOCKFILE_PATH with the project-recommended pnpm version."
  git --no-pager diff -- "$LOCKFILE_PATH" || true
  git --no-pager diff --cached -- "$LOCKFILE_PATH" || true
  exit 1
fi

echo "Lockfile remained unchanged after install."
