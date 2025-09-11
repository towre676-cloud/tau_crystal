BEGIN{ pkg=0 }
function normname(raw,  x){ x=raw; gsub(/^«|»$/,"",x); gsub(/^"|"$/,"",x); return x }
function topstart(l){ return (l ~ /^[[:space:]]*(package|lean_lib|lean_exe|require|script|target|extern_lib)\b/) }
{
  line=$0
  if (topstart(line)) {
    # leaving any skip block
    if (skip) { skip=0 }
    # detect kind + name
    if (line ~ /^[[:space:]]*package[[:space:]]+/) {
      pkg++
      if (pkg>1) { skip=1; print "-- DUPREMOVED " line; next }
    }
    if (line ~ /^[[:space:]]*lean_lib[[:space:]]+/) {
      if (match(line, /^[[:space:]]*lean_lib[[:space:]]+([^[:space:]]+)/, m)) {
        name=normname(m[1]); lib[name]++
        if (lib[name]>1) { skip=1; print "-- DUPREMOVED " line; next }
      }
    }
    if (line ~ /^[[:space:]]*lean_exe[[:space:]]+/) {
      if (match(line, /^[[:space:]]*lean_exe[[:space:]]+([^[:space:]]+)/, m)) {
        ename=normname(m[1]); exe[ename]++
        if (exe[ename]>1) { skip=1; print "-- DUPREMOVED " line; next }
      }
    }
    # first occurrence: print it
    print line; next
  } else {
    # inside body: either skip duplicate block or print
    if (skip) { print "-- DUPREMOVED " line; next } else { print line; next }
  }
}
