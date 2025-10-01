cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
set -euo pipefail; set +H; umask 022; export LC_ALL=C LANG=C
kdir=".ci_keys"; mkdir -p "$kdir"
priv="$kdir/runner_ed25519_priv.pem"; pub="$kdir/runner_ed25519_pub.pem"
if [ ! -s "$priv" ]; then
  openssl genpkey -algorithm Ed25519 -out "$priv" >/dev/null 2>&1 || { echo "[err] openssl Ed25519 not available"; exit 70; }
  openssl pkey -in "$priv" -pubout -out "$pub" >/dev/null 2>&1 || true
fi
ts="$(date -u +%FT%TZ)"; host="$(hostname 2>/dev/null || printf "%s" unknown)"; user="$(whoami 2>/dev/null || printf "%s" unknown)"
git_ref="$(git rev-parse --verify HEAD 2>/dev/null || printf "%s" none)"
os="$(uname -a 2>/dev/null || printf "%s" unknown)"; gha="${GITHUB_ACTIONS:-false}"
out=".tau_ledger/ci/signed_runner/${ts//:/-}_sig.json"; tmp=".tmp.runner_msg.$$"; : > "$tmp"
printf "%s" "ts=$ts|host=$host|user=$user|sha=$git_ref|gha=$gha|os=$os" > "$tmp"
sigbin=".tmp.runner_sig.$$"; : > "$sigbin"
if ! openssl pkeyutl -sign -inkey "$priv" -rawin -in "$tmp" -out "$sigbin" >/dev/null 2>&1; then
  echo "[err] Ed25519 sign failed (openssl pkeyutl)"; rm -f "$tmp" "$sigbin"; exit 71
fi
sigb64="$(base64 -w0 < "$sigbin" 2>/dev/null || base64 < "$sigbin")"
pubpem=""; if [ -s "$pub" ]; then pubpem="$(tr -d "\r" < "$pub" | tr "\n" "|" )"; fi
: > "$out"
printf "%s" "{" >> "$out"
printf "%s" "\"ts\":\"$ts\",\"host\":\"$host\",\"user\":\"$user\",\"git_sha\":\"$git_ref\",\"github_actions\":\"$gha\",\"uname\":\"$(printf "%s" "$os" | sed "s/\"/\047/g")\",\"signature_ed25519\":\"$sigb64\",\"pubkey_pem_pipe\":\"$pubpem\"" >> "$out"
printf "%s" "}" >> "$out"
rm -f "$tmp" "$sigbin"; echo "[ok] signed → $out"
