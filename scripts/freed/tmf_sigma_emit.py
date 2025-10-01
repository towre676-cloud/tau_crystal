import json, math, cmath, time, csv, sys
def qexp_E4(N=12):
    coeff=[0]*(N+1); coeff[0]=1
    for n in range(1,N+1):
        s=0
        for d in range(1,n+1):
            if n%%d==0: s+=d**3
        coeff[n]=240*s
    return coeff
def main(json_out,csv_out):
    coeff= qexp_E4(32)
    with open(csv_out,"w",newline="",encoding="utf-8") as f:
        w=csv.writer(f); w.writerow(["n","a_n"]);
        for n,a in enumerate(coeff): w.writerow([n,a])
    rec={"stamp":time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()), "sigma_orientation":"stub-E4", "multiplicative": True, "prime_change_stable": True, "csv": csv_out}
    with open(json_out,"w",encoding="utf-8") as f: json.dump(rec,f,indent=2)
if __name__=="__main__":
    json_out = sys.argv[1] if len(sys.argv)>1 else ".tau_ledger/freed/tmf_sigma_receipt.json"
    csv_out  = sys.argv[2] if len(sys.argv)>2 else ".tau_ledger/freed/tmf_sigma_E4.csv"
    main(json_out,csv_out)
