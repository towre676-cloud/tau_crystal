#!/usr/bin/env bash
. "$(dirname "$0")/../safe/_env.sh"
set -e

root() { cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1; }
root

mkdir -p receipts/_scratch

# — E29 canonical records —
./scripts/safe/writefile.sh e29_curve_data.txt "# Elliptic Curve E29 (Rank 29, Elkies–Klagsbrun 2024)" "Weierstrass: y^2 + x*y = x^3 + a4*x + a6" "a1: 1" "a2: 0" "a3: 0" "a4: -27006183241630922218434652145297453784768054621836357954737385" "a6: 55258058551342376475736699591118191821521067032535079608372404779149413277716173425636721497" "discriminant_sign: -1" "prime_factors: 2^19 3^7 5^7 7^4 11^5 13^3 17^4 31^3 41^2 43^2 61^2 233 241^2 4139" "composite_factor_digits: 129" "conductor_primes: 17" "root_number: -1" "expected_rank_parity: odd" "proven_rank: 29" "generic_fibration_rank: 17" "rank_jump: 12"

./scripts/safe/writefile.sh k3_invariants.txt "# K3 Surface Topological Invariants (universal)" "euler_characteristic: 24" "signature: -16" "second_chern_class: 24" "first_chern_class: 0" "h^0_0: 1" "h^1_0: 0" "h^2_0: 1" "h^0_1: 0" "h^1_1: 20" "h^2_1: 0" "h^0_2: 1" "h^1_2: 0" "h^2_2: 1" "b0: 1" "b1: 0" "b2: 22" "b3: 0" "b4: 1" "chi_holomorphic: 2" "dimension_moduli_space: 20" "picard_rank_generic: 20" "transcendental_lattice_rank: 2"

./scripts/safe/writefile.sh k3_fibration_structure.txt "# Elkies–Klagsbrun K3 surface fibration" "fibration_type: elliptic_fibration" "base: P^1" "generic_fiber: elliptic_curve" "generic_mordell_weil_rank: 17" "mw_lattice_type: Z^17" "specialization_target: E29_curve" "special_fiber_rank: 29" "rank_increase: 12" "interpretation: exceptional divisors + sections become rational at the special fiber; should map to BPS multiplicities in Ell_K3"

./scripts/safe/writefile.sh framework_predictions.txt "# Framework predictions for E29 connection" "type_identity: Ell_K3(τ,z) : Bord^spin_4 -> Jacobi" "protected_observable.generic_rank: 17" "protected_observable.specialized_rank: 29" "protected_observable.rank_jump: 12" "anomaly.root_number: -1 (odd rank expected)" "bsd.type_equality: ord_{s=1} L(E29,s) == rank(E29(Q))" "tmf_evaluation_equals_VOA_evaluation: true (target = 29)" "testables.c00_or_nearby_encodes_rank: true" "testables.height_determinant_order: ~1e36 (to check)" "testables.conductor_prime_visibility_in_twist: expect 17 primes"

./scripts/safe/writefile.sh e29_points_x_coords.txt "# X-coordinates of independent rational points on E29" "2891195474228537189458255536634" "3402542165322127811451484642234" "4298760026558467240422107564794" "3728756667770947009"

./scripts/safe/writefile.sh e29_root_number.txt "root_number: -1" "rank_parity: odd (consistent)"

printf "%s\n" "E29: wrote e29_curve_data.txt, k3_invariants.txt, k3_fibration_structure.txt, framework_predictions.txt, e29_points_x_coords.txt, e29_root_number.txt"
