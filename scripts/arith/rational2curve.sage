# Consumes schemas/rational_invariants.csv + fixed j_coeffs_Z.txt
# Emits: curve.json per subject/session, coefficients.csv via SEA, and stability_test.csv.
# NOTE: This is a scaffold; fill with concrete SEA calls and Tate's algorithm.

import csv, json, sys, os
print("rational2curve.sage: scaffold. Implement SEA + Tate with pinned Sage version.", file=sys.stderr)
