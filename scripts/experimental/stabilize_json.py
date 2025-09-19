import os, sys, json, pathlib

def extract_first_json_object(text):
    i = text.find("{")
    if i < 0: return None
    depth, in_str, esc = 0, False, False
    buf = []
    for ch in text[i:]:
        buf.append(ch)
        if in_str:
            if esc:
                esc = False
            elif ch == '\\':
                esc = True
            elif ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch == '{':
                depth += 1
            elif ch == '}':
                depth -= 1
                if depth == 0:
                    break
    try:
        return json.loads("".join(buf))
    except json.JSONDecodeError as e:
        print("[decode error]", e)
        return None

def stabilize(src, dst):
    s = pathlib.Path(src).read_text(encoding="utf-8", errors="replace")
    obj = extract_first_json_object(s)
    if obj is None:
        print("[fail]", src, "→ no valid object")
        return False
    txt = json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n"
    tmp = dst + ".tmp"
    pathlib.Path(tmp).write_text(txt, encoding="utf-8")
    os.replace(tmp, dst)
    print("[stable]", dst)
    return True

def main():
    pairs = [
        (".tau_ledger/langlands/combined_ap_satake.json", ".tau_ledger/langlands/combined_ap_satake_stable.json"),
        (".tau_ledger/langlands/ap.json", ".tau_ledger/langlands/ap_stable.json"),
        (".tau_ledger/langlands/satake.json", ".tau_ledger/langlands/satake_stable.json"),
        (".tau_ledger/discovery/confirm_double_zero.json", ".tau_ledger/discovery/confirm_double_zero_stable.json"),
    ]
    for src, dst in pairs:
        if os.path.isfile(src):
            stabilize(src, dst)

if __name__ == "__main__":
    main()
