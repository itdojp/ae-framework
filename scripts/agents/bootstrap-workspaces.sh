#!/usr/bin/env bash
#
# Bootstrap multiple agent workspaces for GitHub-driven collaboration.
# - Creates a parent directory (default: ~/ws)
# - Creates per-agent subdirectories (pm-high, arch-high, impl-1, impl-2, impl-3)
# - Clones the repository into each workspace (read-only mirror of the same repo)
# - Writes an agent-specific setup script (agent-setup.sh) and a simple watcher (watch.sh)
#
# Usage:
#   scripts/agents/bootstrap-workspaces.sh \
#     [-b BASE_DIR] [-r OWNER/REPO] [-p https|ssh] \
#     [-a "pm-high,arch-high,impl-1,impl-2,impl-3"]
#
# Example:
#   scripts/agents/bootstrap-workspaces.sh -b "$HOME/ws" -r itdojp/ae-framework -p https
#
set -euo pipefail

BASE_DIR="${BASE_DIR:-$HOME/ws}"
REPO_SLUG="${REPO_SLUG:-}"
PROTO="${PROTO:-https}"
AGENTS_CSV="${AGENTS_CSV:-pm-high,arch-high,impl-1,impl-2,impl-3}"

while getopts ":b:r:p:a:h" opt; do
  case "$opt" in
    b) BASE_DIR="$OPTARG" ;;
    r) REPO_SLUG="$OPTARG" ;;
    p) PROTO="$OPTARG" ;;
    a) AGENTS_CSV="$OPTARG" ;;
    h)
      sed -n '1,120p' "$0" | sed -n '1,60p'
      exit 0
      ;;
    *) echo "Unknown option: -$OPTARG" >&2; exit 1;;
  esac
done

# Try to infer REPO_SLUG from current git remote if not provided
if [[ -z "$REPO_SLUG" ]]; then
  if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    url=$(git config --get remote.origin.url || true)
    if [[ -n "$url" ]]; then
      # Extract owner/repo from ssh or https URL
      if [[ "$url" =~ ^git@github.com:(.*)\.git$ ]]; then
        REPO_SLUG="${BASH_REMATCH[1]}"
      elif [[ "$url" =~ ^https://github.com/(.*)\.git$ ]]; then
        REPO_SLUG="${BASH_REMATCH[1]}"
      elif [[ "$url" =~ ^https://github.com/([^/]+/[^/]+)$ ]]; then
        REPO_SLUG="${BASH_REMATCH[1]}"
      fi
    fi
  fi
fi

if [[ -z "$REPO_SLUG" ]]; then
  echo "REPO_SLUG not provided and could not be inferred. Use -r owner/repo" >&2
  exit 2
fi

if [[ "$PROTO" != "https" && "$PROTO" != "ssh" ]]; then
  echo "Invalid protocol: $PROTO (use https or ssh)" >&2
  exit 2
fi

IFS=',' read -r -a AGENTS <<< "$AGENTS_CSV"

echo "Base dir: $BASE_DIR"
echo "Repo: $REPO_SLUG"
echo "Protocol: $PROTO"
echo "Agents: ${AGENTS[*]}"

mkdir -p "$BASE_DIR"

clone_url() {
  local slug="$1"
  if [[ "$PROTO" == "ssh" ]]; then
    echo "git@github.com:$slug.git"
  else
    echo "https://github.com/$slug.git"
  fi
}

role_label_for() {
  case "$1" in
    pm-high) echo "role:PM-HIGH" ;;
    arch-high) echo "role:ARCH-HIGH" ;;
    impl-1) echo "role:IMPL-MED-1" ;;
    impl-2) echo "role:IMPL-MED-2" ;;
    impl-3) echo "role:IMPL-MED-3" ;;
    *) echo "role:UNKNOWN" ;;
  esac
}

for agent in "${AGENTS[@]}"; do
  ws="$BASE_DIR/$agent"
  printf "\n==> Preparing workspace: %s\n" "$ws"
  mkdir -p "$ws"

  repo_dir="${REPO_SLUG##*/}"
  if [[ ! -d "$ws/$repo_dir/.git" ]]; then
    echo "Cloning $REPO_SLUG into $ws/$repo_dir"
    git clone "$(clone_url "$REPO_SLUG")" "$ws/$repo_dir"
  else
    echo "Repo exists. Fetching updates..."
    (cd "$ws/$repo_dir" && git fetch --all --prune)
  fi

  # Write per-agent environment file
  cat > "$ws/agent.env" <<EOF
# Per-agent environment
export GH_REPO="$REPO_SLUG"
export AGENT_NAME="$agent"
export AGENT_ROLE="$(role_label_for "$agent")"
# Optional feature flags
# export AE_FEATURE_RECONCILE=1
# export AE_FEATURE_MODEL_EVAL=1
EOF

  # Write per-agent setup script
  cat > "$ws/agent-setup.sh" <<'EOS'
#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
if [[ -f "$here/agent.env" ]]; then
  # shellcheck disable=SC1091
  source "$here/agent.env"
else
  echo "agent.env not found. Please create it first." >&2
  exit 1
fi

repo_slug=$(grep -E "^\s*(export\s+)?GH_REPO\s*=\s*" "$here/agent.env" | tail -n1 | sed -E 's/.*=\s*"?([^"\s]+)"?.*/\1/')
repo_dir="${repo_slug##*/}"
cd "$here/$repo_dir"

# Configure git identity (local to this repo)
git config user.name "agent-${AGENT_NAME}"
git config user.email "agent-${AGENT_NAME}@example.invalid"

echo "Git identity configured for ${AGENT_NAME}" 

echo "Checking gh authentication..."
if ! gh auth status -h github.com >/dev/null 2>&1; then
  echo "gh is not authenticated. You can log in with: gh auth login --web"
fi

echo "Repository: ${GH_REPO}" 
echo "Agent Role: ${AGENT_ROLE}"
echo "Setup complete. You can run ./watch.sh to auto-start on ready issues."
EOS
  chmod +x "$ws/agent-setup.sh"

  # Write a simple watcher script
  cat > "$ws/watch.sh" <<'EOS'
#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
# shellcheck disable=SC1091
source "$here/agent.env"

if ! command -v gh >/dev/null 2>&1; then
  echo "gh CLI not found in PATH" >&2
  exit 2
fi

if ! command -v jq >/dev/null 2>&1; then
  echo "jq is required but not found in PATH" >&2
  exit 2
fi
echo "Watcher started for $AGENT_NAME ($AGENT_ROLE) on $GH_REPO"

while true; do
  mapfile -t issues < <(gh issue list --repo "$GH_REPO" \
    --label "$AGENT_ROLE" --label status:ready \
    --json number,title | jq -r '.[].number')

  if [[ ${#issues[@]} -gt 0 && -n "${issues[0]:-}" ]]; then
    for N in "${issues[@]}"; do
      echo "Processing issue #$N ..."
      gh issue comment "$N" --repo "$GH_REPO" --body "/start" || true
    done
  fi

  sleep 60
done
EOS
  chmod +x "$ws/watch.sh"

  # Write a quick README
  cat > "$ws/README_AGENT.md" <<EOF
# Agent Workspace: $agent

Role Label: $(role_label_for "$agent")
Repository: $REPO_SLUG

## Quickstart
1. Edit agent.env if needed
2. Run setup:   ./agent-setup.sh
3. Start watch: ./watch.sh   # polls GitHub for issues with labels: [role, status:ready]

Notes:
- gh auth login --web    # if gh is not authenticated
- Clone dir: $repo_dir/
EOF

done

printf "\nAll workspaces prepared under: %s\n" "$BASE_DIR"
