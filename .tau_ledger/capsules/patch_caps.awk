BEGIN{FS=OFS="\t"}
NR==1 {print; next}
$1=="capsules_verify" {print $1, s, (s=="ok"?t:"-"), (s=="ok"?"-":e); next}
{print}
