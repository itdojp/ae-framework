#!/bin/bash

# Utility helpers shared by KvOnce trace scripts and workflows.
kvonce_resolve_path() {
  local target="$1"
  if [[ -z "${KVONCE_REALPATH_CMD:-}" ]]; then
    if command -v realpath >/dev/null 2>&1; then
      KVONCE_REALPATH_CMD="realpath"
    elif command -v python3 >/dev/null 2>&1; then
      KVONCE_REALPATH_CMD="python3"
    else
      KVONCE_REALPATH_CMD="python"
    fi
  fi

  if [[ "${KVONCE_REALPATH_CMD}" == "realpath" ]]; then
    realpath "$target"
  else
    "${KVONCE_REALPATH_CMD}" -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$target"
  fi
}
