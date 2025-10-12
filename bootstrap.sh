#!/usr/bin/env bash
# τ-Crystal bootstrap: safe POSIX shell setup for cross-platform operation
# Usage: ./bootstrap.sh [command]

set -euo pipefail
set +H
umask 022
export LC_ALL=C

# Detect repo root robustly
if [ -n "${BASH_SOURCE:-}" ]; then
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
else
    SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
fi

REPO_ROOT="${SCRIPT_DIR}"
cd "${REPO_ROOT}" || {
    echo "ERROR: Cannot navigate to repo root: ${REPO_ROOT}" >&2
    exit 1
}

# Validate we are in a git repository
if ! git rev-parse --git-dir >/dev/null 2>&1; then
    echo "ERROR: Not in a git repository" >&2
    exit 1
fi

# Safe path resolution (Windows-compatible)
normalize_path() {
    local p="$1"
    echo "$p" | sed -e "s|/\./|/|g" -e "s|//*|/|g" -e "s|/$||"
}

# Echo with timestamp (safe for all platforms)
log() {
    printf "[%s] %s\n" "$(date -u "+%Y-%m-%d %H:%M:%S UTC")" "$*"
}

# Verify critical files exist
verify_structure() {
    local required_files=(
        "README.md"
        ".git"
    )
    for f in "${required_files[@]}"; do
        if [ ! -e "${REPO_ROOT}/${f}" ]; then
            echo "WARNING: Expected file/dir not found: ${f}" >&2
        fi
    done
}

main() {
    log "τ-Crystal bootstrap initialized"
    log "Repository root: ${REPO_ROOT}"
    log "Shell: ${SHELL:-unknown}"
    log "Platform: $(uname -s 2>/dev/null || echo "unknown")"
    verify_structure
    if [ $# -gt 0 ]; then
        case "$1" in
            test)
                log "Bootstrap test: PASS"
                ;;
            info)
                git rev-parse --short HEAD 2>/dev/null || echo "No git HEAD"
                ;;
            *)
                echo "Unknown command: $1" >&2
                echo "Available: test, info" >&2
                exit 1
                ;;
        esac
    fi
    log "Bootstrap complete"
}
main "$@"
