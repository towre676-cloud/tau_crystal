BEGIN{print "PR    | labels                         | draft | mergeable        | url"; print "----- | ------------------------------ | ----- | ---------------- | ---"}
{ lbl=$2; if (lbl=="") lbl="none"; printf "#%-4s | %-30s | %-5s | %-16s | %s\n", $1, lbl, $3, $4, $5 }
