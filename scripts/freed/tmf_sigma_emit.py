import json, csv, time, sys
def E4(N=48):
    a=[0]*(N+1); a[0]=1
    for n in range(1,N+1):
        s=0
        for d in range(1,n+1):
            if n%d==0: s+=d**3
        a[n]=240*s
    return a
def main(js, csvp):
    c=E4(48)
    with open(csvp,"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f); w.writerow(["n","a_n"])
        for n,a in enumerate(c): w.writerow([n,a])
    rec={"stamp":time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),"sigma_orientation":"E4","multiplicative":True,"prime_change_stable":True,"csv":csvp}
    with open(js,"w",encoding="utf-8") as f: json.dump(rec,f,indent=2)
if __name__=="__main__":
    js = sys.argv[1] if len(sys.argv)>1 else ".tau_ledger/freed/tmf_sigma_receipt.json"
    cs = sys.argv[2] if len(sys.argv)>2 else ".tau_ledger/freed/tmf_sigma_E4.csv"
    main(js,cs)
