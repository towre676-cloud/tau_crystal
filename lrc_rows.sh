#!/usr/bin/env sh
CSV="$1"
awk -F, 'NR>1{c++} END{print (c+0)}' "$CSV"
