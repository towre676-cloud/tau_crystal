cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; umask 022; export LC_ALL=C LANG=C
j="${1:-}"; if [ -z "$j" ]; then j=$(ls -1 .tau_ledger/ci/signed_runner/*_sig.json 2>/dev/null | tail -n 1 || true); fi
[ -s "$j" ] || { echo "[err] no runner receipt found"; exit 2; }
val() { sed -n "s/.*\"$1\":\"\\([^\"]*\\)\".*/\\1/p" "$j" | head -n1; }
ts=$(val ts); host=$(val host); user=$(val user); sha=$(val git_sha); gha=$(val github_actions); unamef=$(val uname)
sigb64=$(val signature_ed25519); pubpipe=$(val pubkey_pem_pipe)
[ -n "$ts" ] || { echo "[err] bad receipt (ts)"; exit 3; }
msg="ts=$ts|host=$host|user=$user|sha=$sha|gha=$gha|os=$unamef"; printf "%s" "$msg" > .tmp.msg.$$
base64 -d <(printf "%s" "$sigb64") > .tmp.sig.$$ 2>/dev/null || base64 -D -o .tmp.sig.$$ <(printf "%s" "$sigb64") 2>/dev/null || { echo "[err] base64 decode failed"; exit 4; }
pub=".ci_keys/runner_ed25519_pub.pem"; if [ ! -s "$pub" ] && [ -n "$pubpipe" ]; then printf "%s\n" "$pubpipe" | tr "|" "\n" > "$pub"; fi
[ -s "$pub" ] || { echo "[err] no pubkey"; exit 5; }
if openssl pkeyutl -verify -pubin -inkey "$pub" -rawin -in .tmp.msg.$$ -sigfile .tmp.sig.$$ >/dev/null 2>&1; then echo "[ok] signature verified for $j"; rc=0; else echo "[err] verification failed for $j"; rc=6; fi
rm -f .tmp.msg.$$ .tmp.sig.$$; exit $rc
