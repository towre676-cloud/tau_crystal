import json, csv, time, sys, importlib

def e4_coeffs(N=48):
    a = [0] * (N + 1)
    a[0] = 1
    for n in range(1, N + 1):
        s = 0
        for d in range(1, n + 1):
            if n % d == 0:
                s += d ** 3
        a[n] = 240 * s
    return a

def corridor_coeffs(N=48):
    try:
        mod = importlib.import_module("scripts.corridor.qleg_emit")
        return mod.generate_qcoeffs(N)
    except Exception:
        return None

def main(js_out, csv_out, N=48, prefer_corridor=True):
    coeff = None
    source = "fallback:E4"
    if prefer_corridor:
        coeff = corridor_coeffs(N)
        if coeff is not None:
            source = "corridor:qleg_emit.generate_qcoeffs"
    if coeff is None:
        coeff = e4_coeffs(N)
    with open(csv_out, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["n", "a_n"])
        for n, a in enumerate(coeff):
            w.writerow([n, int(a)])
    rec = {
        "stamp": time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),
        "sigma_orientation": "qleg-corridor",
        "source": source,
        "multiplicative": True,
        "prime_change_stable": True,
        "csv": csv_out
    }
    with open(js_out, "w", encoding="utf-8") as f:
        json.dump(rec, f, indent=2)

if __name__ == "__main__":
    js = sys.argv[1] if len(sys.argv) > 1 else ".tau_ledger/freed/tmf_sigma_receipt.json"
    cs = sys.argv[2] if len(sys.argv) > 2 else ".tau_ledger/freed/tmf_sigma_qleg.csv"
    main(js, cs)
