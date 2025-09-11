#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
hook=".git/hooks/pre-commit"
bak=".git/hooks/pre-commit.bak"
[ -f "$hook" ] && cp -f "$hook" "$bak" || true
: > "$hook"
chmod +x "$hook"
printf "%s\n" "#!/usr/bin/env bash" >> "$hook"
printf "%s\n" "set -euo pipefail" >> "$hook"
printf "%s\n" "files=\$(git diff --cached --name-only --diff-filter=ACM | grep -E \"^out/.*\\.json\$\" || true)" >> "$hook"
printf "%s\n" "[ -n \"\$files\" ] || exit 0" >> "$hook"
printf "%s\n" "echo \"[pre-commit] gating:\"" >> "$hook"
printf "%s\n" "echo \"\$files\" | tr \" \" \"\\n\" | while read -r f; do bash scripts/tau_gate.sh --verbose \"\$f\"; done" >> "$hook"
printf "%s\n" "echo \"[pre-commit] all gated ✔\"" >> "$hook"
echo "[install] pre-commit hook installed → .git/hooks/pre-commit"
