import sys, json, io
def zm(section):
    total = 0
    for t in section:
        try: n,r,c = t
        except Exception:
            continue
        if n == 0:
            try: total += int(c)
            except Exception:
                try: total += float(c)
                except Exception: pass
    return int(total)
if __name__ == "__main__":
    coeffs_path = sys.argv[1]
    out_path    = sys.argv[2]
    with io.open(coeffs_path,"r",encoding="utf-8") as fh:
        data = json.load(fh)
    g = data.get("generic", [])
    t = data.get("twisted", [])
    res = {"schema":"tau_crystal.elliptic_genus.v1","surface":data.get("surface",""),"generic":{"zero_modes":zm(g)},"twisted":{"zero_modes":zm(t)}}
    with io.open(out_path,"w",encoding="utf-8") as fo:
        fo.write(json.dumps(res, ensure_ascii=False, separators=(",",":")) + "\n")
