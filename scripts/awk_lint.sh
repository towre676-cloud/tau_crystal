#!/usr/bin/env bash
gawk -W lint=fatal -v Y0=0 -v SIG0=1 -v DMAX0=1 -v PMAX0=1 -v MDL0=0 -v Z0v=0 -v Z1v=0 -v Z2v=0 -v Z3v=0 -v Z4v=0 -f scripts/ulp_search.awk </dev/null
