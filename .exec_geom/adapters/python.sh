#!/usr/bin/env bash
set -euo pipefail; set +H; umask 022
W=${1:-.}
EXC=.exec_geom/exceptionals.tsv; SYM=.exec_geom/symbol.conf
