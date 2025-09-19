BEGIN{FS="\t"; f=0}
$1==key{print $2; f=1; exit}
END{if(!f)print def}
