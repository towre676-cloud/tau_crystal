#!/usr/bin/env bash
remote="${1:-origin}"
echo "[push] remote: $remote"
git remote get-url "$remote" >/dev/null || { echo "[push] remote '$remote' not found"; exit 1; }
secret_paths=( ".tau_ledger/ed25519_sk.pem" ".tau_ledger/ed25519_priv.pem" ".ssh/id_ed25519" ".ssh/id_rsa" )
echo "[guard] scanning LOCAL refs (branches+tags) for sensitive paths…"
if git log --branches --tags --name-only --pretty=format: -- "${secret_paths[@]}" | grep -q .; then
  echo "[ABORT] a sensitive path still exists on LOCAL refs. Re-run filter-repo."; exit 2
fi
git fetch "$remote" --prune
if [ -s analysis/forensics/dangling.tsv ]; then
  echo "[push] creating recover/* refs from analysis/forensics/dangling.tsv…"
  while IFS=$'\t' read -r _ sha _; do
    [ -n "$sha" ] || continue
    ref="recover/${sha:0:8}"
    git show-ref --verify --quiet "refs/heads/$ref" || git branch "$ref" "$sha" || true
  done < <(cut -f1-2 analysis/forensics/dangling.tsv)
fi
archive_local="backup/main-8afd567"
archive_remote="archive/backup-main-8afd567"
have_archive_local=0; git show-ref --verify --quiet "refs/heads/$archive_local" && have_archive_local=1
echo "[push] force-pushing branches…"
while read -r b; do
  [ "$b" = "$archive_local" ] && continue
  echo "  -> $b"
  git push "$remote" --force "refs/heads/$b:refs/heads/$b" || echo "  [!] failed $b"
done < <(git for-each-ref --format='%(refname:short)' refs/heads)
if [ "$have_archive_local" -eq 1 ]; then
  echo "[push] archiving $archive_local -> $archive_remote"
  git push "$remote" --force "refs/heads/$archive_local:refs/heads/$archive_remote" && echo "  [+] archived as $remote/$archive_remote"
fi
echo "[push] force-pushing recover/*…"
git for-each-ref --format='%(refname:short)' refs/heads/recover/ | while read -r r; do
  git push "$remote" --force "refs/heads/$r:refs/heads/$r" && echo "  [+] $r" || echo "  [!] $r failed"
done
echo "[push] pushing tags…"
git push --force --tags "$remote" || true
if git ls-remote --heads "$remote" | grep -q 'refs/heads/backup/main-8afd567'; then
  echo "[push] (optional) deleting old remote backup/main-8afd567 to remove pre-scrub ref"
  git push "$remote" --delete backup/main-8afd567 || true
fi
echo "[push] done. Remote heads now include:"
git ls-remote --heads "$remote" | awk '{print $2}' | sed 's|refs/heads/|  - |' | sort
