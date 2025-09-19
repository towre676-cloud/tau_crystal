BEGIN{ FS=","; OFS="," }
function trim(s){gsub(/^[[:space:]]+|[[:space:]]+$/,"",s);return s}
function deq(s){gsub(/^"|"$/,"",s);return s}
function isnum(s){return (s ~ /^[+-]?[0-9]*\.?[0-9]+([eE][+-]?[0-9]+)?$/)}
NR==1{next}                                       # skip header
{
  for(i=1;i<=NF;i++) $i=trim(deq($i))
  sub(/\r$/,"",$NF)                                # tolerate CRLF
  file=$1; pt=$2; x=$3; y=$4
  if(!isnum(x) || !isnum(y)) next                  # need numeric coordinates
  if(file ~ LP){ Lx[pt]=x; Ly[pt]=y; seenL++ }
  if(file ~ RP){ Rx[pt]=x; Ry[pt]=y; seenR++ }
}
END{
  if(seenL==0 || seenR==0){ print "no rows matched LP/RP patterns", LP, RP > "/dev/stderr"; exit 4 }
  olap=0; for(k in Lx) if(k in Rx) olap++
  if(olap<3){ print "fewer than 3 matched point pairs (overlap=" olap ", L=" seenL ", R=" seenR ")", LP, RP > "/dev/stderr"; exit 5 }
  # deterministic order (lexicographic keys; points may be names)
  n=0; for(k in Lx) if(k in Rx){ n++; keys[n]=k }
  for(i=1;i<=n;i++) for(j=i+1;j<=n;j++) if(keys[i] > keys[j]){ t=keys[i]; keys[i]=keys[j]; keys[j]=t }
  for(i=1;i<=n;i++){ p=keys[i]; print Lx[p],Ly[p],Rx[p],Ry[p] }
}
