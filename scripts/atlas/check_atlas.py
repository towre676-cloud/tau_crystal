#!/usr/bin/env python3
import csv, sys, os, json, math, hashlib

csv_path = "docs/equation_atlas.csv"
missing = []
with open(csv_path, newline="", encoding="utf-8") as f:
    rows = list(csv.DictReader(f))
for r in rows:
    repo = r["Repo"]
    if not os.path.exists(repo.split(",")[0].split()[0]):
        missing.append((r["EqID"], repo))
if missing:
    print("Missing anchors:", missing)
    sys.exit(2)
print("Equation Atlas anchors present:", len(rows))

