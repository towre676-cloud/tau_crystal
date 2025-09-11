#!/usr/bin/env python3
import sys, json, pathlib, argparse
p = argparse.ArgumentParser()
p.add_argument("out")
p.add_argument("-i","--infile")
p.add_argument("--ascii", type=int, choices=[0,1], default=0)
a = p.parse_args()
src = pathlib.Path(a.infile).read_bytes() if a.infile else sys.stdin.buffer.read()
obj = json.loads(src.decode("utf-8"))
s = json.dumps(obj, sort_keys=True, separators=(",",":"), ensure_ascii=bool(a.ascii))
pathlib.Path(a.out).write_bytes(s.encode("utf-8"))
