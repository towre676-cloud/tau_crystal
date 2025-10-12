#!/usr/bin/env bash
# τ-Crystal verification: ensure repository integrity
# Usage: ./scripts/verify.sh

set -euo pipefail
set +H
umask 022
export LC_ALL=C

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

if [ -f "${SCRIPT_DIR}/utils.sh" ]; then
    # shellcheck source=scripts/utils.sh
    source "${SCRIPT_DIR}/utils.sh"
else
    log_info()  { echo "[INFO] $*"; }
    log_ok()    { echo "[OK] $*"; }
    log_warn()  { echo "[WARN] $*" >&2; }
    log_error() { echo "[ERROR] $*" >&2; }
    log_fatal() { log_error "$@"; exit 1; }
fi

cd "${REPO_ROOT}" || log_fatal "Cannot cd to repo root"

verify_git() {
    log_info "Verifying git repository"
    if ! git rev-parse --git-dir >/dev/null 2>&1; then
        log_error "Not a git repository"
        return 1
    fi
    local branch
    branch="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")"
    log_ok "Git repository OK (branch: ${branch})"
    return 0
}

verify_shell_scripts() {
    log_info "Verifying shell scripts"
    local scripts=(
        "bootstrap.sh"
        "scripts/utils.sh"
        "scripts/verify.sh"
    )
    local found=0
    local total=0
    for script in "${scripts[@]}"; do
        total=$((total + 1))
        if [ -f "${REPO_ROOT}/${script}" ]; then
            found=$((found + 1))
            if [ -x "${REPO_ROOT}/${script}" ]; then
                log_ok "Found executable: ${script}"
            else
                log_info "Found (not executable): ${script}"
            fi
            if bash -n "${REPO_ROOT}/${script}" 2>/dev/null; then
                log_ok "Syntax OK: ${script}"
            else
                log_error "Syntax error in: ${script}"
                return 1
            fi
        else
            log_error "Missing: ${script}"
        fi
    done
    log_info "Shell scripts: ${found}/${total} found"
    return 0
}

verify_structure() {
    log_info "Verifying repository structure"
    local critical_paths=(
        ".git"
        "README.md"
    )
    local all_ok=0
    for path in "${critical_paths[@]}"; do
        if [ -e "${REPO_ROOT}/${path}" ]; then
            log_ok "Found: ${path}"
        else
            log_error "Missing: ${path}"
            all_ok=1
        fi
    done
    return $all_ok
}

verify_platform() {
    log_info "Platform information"
    local os; os="$(uname -s 2>/dev/null || echo "unknown")"
    log_info "OS: ${os}"
    local shell_path="${SHELL:-unknown}"
    log_info "Shell: ${shell_path}"
    if command -v bash >/dev/null 2>&1; then
        local bash_version; bash_version="$(bash --version | head -n1)"
        log_ok "Bash available: ${bash_version}"
    else
        log_warn "Bash not found in PATH"
    fi
    return 0
}

main() {
    log_info "τ-Crystal repository verification"
    log_info "Repository root: ${REPO_ROOT}"
    echo
    local exit_code=0
    verify_platform || exit_code=1
    echo
    verify_git || exit_code=1
    echo
    verify_structure || exit_code=1
    echo
    verify_shell_scripts || exit_code=1
    echo
    if [ $exit_code -eq 0 ]; then
        log_ok "All verifications passed"
    else
        log_error "Some verifications failed"
    fi
    return $exit_code
}
main "$@"
