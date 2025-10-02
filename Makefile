.PHONY: heo test optional receipts

heo:
	python ci/heo/scripts/compute_density.py --sequence ci/data/sequences/periodic_7_0010010.json --d 2 --k 0 --assert-bounds 0 1
	python ci/heo/scripts/compute_pressure.py --sequence ci/data/sequences/periodic_7_0010010.json --beta 0.7

test: heo
	python ci/heo/scripts/finite_surgery_test.py
	python ci/heo/scripts/thinning_bound_test.py --sequence ci/data/sequences/periodic_7_0010010.json --thinning ci/data/sequences/thinning_maps.json
	python ci/heo/scripts/periodic_rationality_test.py --sequence ci/data/sequences/periodic_7_0010010.json

optional:
	- python ci/heo/scripts/residue_density_test.py
	- python ci/heo/scripts/p_adic_limsup_probe.py
	- python ci/heo/scripts/brocard_fixture.py

receipts:
	python - <<'PY'
import json, glob
for f in glob.glob("receipts/heo/**/**/*.json", recursive=True):
    print(">>", f)
    print(open(f).read())
PY
