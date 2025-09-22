#!/usr/bin/env bash
set -euo pipefail; set +H
LIST="$1"; OUTBIN="$2"; RECEIPT="$3"
rm -f "$OUTBIN" "$RECEIPT"; touch "$OUTBIN"
while IFS= read -r row; do [ -z "$row" ] && continue; printf "%s\n" "$row" >> "$OUTBIN"; done < "$LIST"
H=$(sha256sum "$OUTBIN" | awk '{print $1}')
printf "%s\n" "time	$(date -u +%FT%TZ)" "dataset	$OUTBIN" "sha256	$H" > "$RECEIPT"
printf "%s\n" "op_return_hex	6a20$H" "broadcast_instructions	use your wallet to push OP_RETURN with this data" >> "$RECEIPT"
echo "$OUTBIN"
