#!/usr/bin/env bash
# τ-Crystal utility functions: minimal, safe, cross-platform
# Source this file: source scripts/utils.sh

if [ -n "${TAU_UTILS_LOADED:-}" ]; then
    return 0
fi
export TAU_UTILS_LOADED=1

set -euo pipefail
set +H
umask 022
export LC_ALL=C

if [ -t 1 ] && command -v tput >/dev/null 2>&1; then
    RED=$(tput setaf 1 2>/dev/null || echo "")
    GREEN=$(tput setaf 2 2>/dev/null || echo "")
    YELLOW=$(tput setaf 3 2>/dev/null || echo "")
    BLUE=$(tput setaf 4 2>/dev/null || echo "")
    RESET=$(tput sgr0 2>/dev/null || echo "")
else
    RED=""
    GREEN=""
    YELLOW=""
    BLUE=""
    RESET=""
fi

log_info()  { printf "%s[INFO]%s %s\n"  "${BLUE}"  "${RESET}" "$*"; }
log_ok()    { printf "%s[OK]%s %s\n"    "${GREEN}" "${RESET}" "$*"; }
log_warn()  { printf "%s[WARN]%s %s\n"  "${YELLOW}" "${RESET}" "$*" >&2; }
log_error() { printf "%s[ERROR]%s %s\n" "${RED}"   "${RESET}" "$*" >&2; }
log_fatal() { log_error "$@"; exit 1; }

run_safe() {
    log_info "Running: $*"
    if "$@"; then
        log_ok "Success: $1"
        return 0
    else
        log_error "Failed: $1 (exit $?)"
        return 1
    fi
}

has_command() { command -v "$1" >/dev/null 2>&1; }
require_command() { has_command "$1" || log_fatal "Required command not found: $1"; }

git_require_clean() {
    if ! git diff-index --quiet HEAD -- 2>/dev/null; then
        log_fatal "Git working directory not clean. Commit or stash changes."
    fi
}
git_current_branch() { git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "HEAD"; }
git_short_hash()   { git rev-parse --short HEAD 2>/dev/null || echo "unknown"; }

ensure_dir() {
    local dir="$1"
    if [ ! -d "$dir" ]; then
        mkdir -p "$dir" || log_fatal "Cannot create directory: $dir"
        log_info "Created directory: $dir"
    fi
}
safe_write() {
    local file="$1"; local content="$2"; local dir
    dir="$(dirname "$file")"
    ensure_dir "$dir"
    printf "%s" "$content" > "$file" || log_fatal "Cannot write file: $file"
}

verify_file_exists() { [ -f "$1" ] || { log_error "Required file not found: $1"; return 1; }; }
verify_dir_exists()  { [ -d "$1" ] || { log_error "Required directory not found: $1"; return 1; }; }

is_windows() { case "$(uname -s 2>/dev/null)" in MINGW*|MSYS*|CYGWIN*) return 0 ;; *) return 1 ;; esac; }
is_linux()   { [ "$(uname -s 2>/dev/null)" = "Linux" ]; }
is_macos()   { [ "$(uname -s 2>/dev/null)" = "Darwin" ]; }

log_ok "τ-Crystal utilities loaded"
