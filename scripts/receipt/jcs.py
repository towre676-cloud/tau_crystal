#!/usr/bin/env python3
import sys, json
def load(path):
    if path == "-":
        return json.loads(sys.stdin.read())
    with open(path, "r", encoding="utf-8") as fh:
        return json.loads(fh.read())
def assert_finite(x):
    if isinstance(x, float):
        if (x != x) or (x == float("inf")) or (x == float("-inf")):
            raise ValueError("Non-finite float in JSON")
    elif isinstance(x, (int, str, bool)) or x is None:
        return
    elif isinstance(x, list):
        for y in x: assert_finite(y)
    elif isinstance(x, dict):
        for y in x.values(): assert_finite(y)
    else:
        raise TypeError(f"Unsupported type in JSON: {type(x)!r}")
def canon(obj):
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, allow_nan=False, separators=(",", ":"))
def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "-"
    obj = load(path)
    assert_finite(obj)
    out = canon(obj)
    sys.stdout.write(out)
    if not out.endswith("\\n"): sys.stdout.write("\\n")
if __name__ == "__main__":
    main()
