docs/specs/heo_universal_structure.md
docs/specs/steel_equations.md

receipts/
  heo/
    defs/
      H_global.json
      H_p_adic.json
      degree_ghost_divisor.json
      pressure.json
    theorems/
      finite_implies_zero.json
      finite_surgery_invariance.json
      thinning_bound.json
      periodic_rationality.json
      residue_equals_density.json   # conditional
    conjectures/
      motivic_degree.json
      weight_density.json
      spectral_action_coupling.json
      arithmetic_rigidity.json

ci/
  heo/
    schemas/
      receipt.schema.json
      test-result.schema.json
    scripts/
      parse_equations.py
      compute_density.py
      compute_pressure.py
      periodic_rationality_test.py
      thinning_bound_test.py
      finite_surgery_test.py
      residue_density_test.py       # conditional
      p_adic_limsup_probe.py
      brocard_fixture.py
      report_receipts.py
  data/
    sequences/
      periodic_7_0010010.json
      polynomial_ax_plus_b.json
      factorial_cutoff.json
      thinning_maps.json
