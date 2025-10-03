#!/usr/bin/env bash
set -e; set +H; umask 022
scripts/tools/py.sh scripts/audit/curvature_json.py
