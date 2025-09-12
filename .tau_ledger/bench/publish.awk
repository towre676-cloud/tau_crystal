function add(k,v,m){ if(m=="cold"){ c[k,++cc[k]]=v } else { w[k,++wc[k]]=v } }
function med(mode,k,  n,i){ n=(mode=="cold"?cc[k]:wc[k]); if(!n) return "NA"; for(i=1;i<=n;i++) t[i]=(mode=="cold"?c[k,i]:w[k,i]); asort(t); return (n%2)? t[(n+1)/2] : int((t[n/2]+t[n/2+1])/2) }
function cnt(mode,k){ return (mode=="cold")?cc[k]+0:wc[k]+0 }
function ratio(mc,mw){ if(mc=="NA"||mw=="NA"||mw==0) return "NA"; return sprintf("%.2f", mc/mw) }
BEGIN{ print "# CI speed benchmarks (receipt-backed)\n"; print "All entries are medians over attested runs from `.tau_ledger/bench/runs.ndjson`. The acceleration factor is cold/warm. Conditions: unchanged mathlib revision; same commit; identical runner image.\n"; print "| OS | Runner | N(cold) | median_cold_s | N(warm) | median_warm_s | factor (cold/warm) |"; print "|---|---|---:|---:|---:|---:|---:|" }
{ if (match($0, /"os":"([^"]+)".*"mode":"([^"]+)".*"runner":"([^"]+)".*"duration_s":([0-9]+)/, a)) { k=a[1] "|" a[3]; add(k, a[4]+0, a[2]); os[k]=a[1]; ru[k]=a[3]; seen[k]=1 } }
END{ if (length(seen)==0){ print "| NA | NA | 0 | NA | 0 | NA | NA |"; exit } for (k in seen) keys[++n]=k; asort(keys); for (i=1;i<=n;i++){ k=keys[i]; mc=med("cold",k); mw=med("warm",k); nc=cnt("cold",k); nw=cnt("warm",k); printf("| %s | %s | %s | %s | %s | %s | %s |\n", os[k], ru[k], nc, mc, nw, mw, ratio(mc,mw)) } }
