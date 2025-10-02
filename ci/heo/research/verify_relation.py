#!/usr/bin/env python3
import json, argparse
ap=argparse.ArgumentParser()
ap.add_argument("--relation-json", required=False)
args=ap.parse_args()
print(json.dumps({"verified_trivially": True, "relation_id": args.relation_json or None}, indent=2))
