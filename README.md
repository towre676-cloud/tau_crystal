## tau-Crystal: Publishable Receipts (Bash-only, reproducible)

This repository emits cryptographically sealed receipts for differential-character evaluations. Each run produces a phase holonomy phase_frac in [0,1) and a Merkle root root_sha256. Below are single-line commands and the exact outputs observed (UTC 2025-10-12).

### Reproduce (single lines)

    bash
if command -v sed >/dev/null 2>&1; then sed -i 's/\r$//' scripts/*.sh 2>/dev/null; fi
    bash scripts/dchar_loop.sh --steps 64 --seed 0
    bash scripts/dchar_loop.sh --steps 64 --seed 1
    bash scripts/dchar_naturality.sh 8 0
    bash scripts/dchar_refine.sh 0 "8,16,32,64"
    bash scripts/dchar_family.sh family-A
    bash scripts/dchar_family.sh family-B
    bash scripts/dchar_modcov.sh S   --weight 0 --index 1
    bash scripts/dchar_modcov.sh T:3 --weight 0 --index 1
printf 'u\ta\ta1\ta2\tp2\tp1\tp0\tseed\n1\t1\t1\t1\t1\t0\t-1\tswpf0\n2\t1\t0\t-1\t1\t0\t-1\tswpf0\n' > A.tsv
cp A.tsv B.tsv
    bash scripts/sw_certify.sh A.tsv B.tsv A B swpf0
    bash scripts/sw_diff_first.sh A.tsv B.tsv swpf0
    # end code block marker removed

Concrete outputs

Loop (64, seed=0) phase=0.78046652137361971
root=84ee1af070361da899c4a3332bc032d84fddd79acdcd28f64a9e4ef20c870c0c
receipt=.tau_ledger/dchar/20251012T184958Z/loop.receipt

Loop (64, seed=1) phase=0.92321435075895164
root=30a4414d8917b75e89a29ba2602cdd4d0050bfc8214fd9a072fff9a80e2232cd
receipt=.tau_ledger/dchar/20251012T185017Z/loop.receipt

Naturality (8,0) TTY=piped:
phase=0.10560301851704734,
root=19cb38b0c9e4b28185a6d3f8e5740069996099308e06b6971cb8c5a4711b431b
receipts: .../20251012T185021Z/loop.receipt, .../20251012T185024Z/loop.receipt

Family 5x4
A: b6cb2e0fad4f294c52059443b9d1df015f00c0fc9938076ce79284c6c75192a9 (.../20251012T185031Z/family.receipt)
B: 28d161e4930640aaf5a18b36351ba82a8d9b0551880ad8bf3c980d6a7447fdb0 (.../20251012T185035Z/family.receipt)

Modular scaffold (canonicalized)
S: a9d9613308696e0253d5cd541092e2e0fbf00ca2129f0977fa7b2b70092de7ae
T^3: 47ab6832a17f73e673111d0dddc92ea3b3082e0620a89bd98a1070269607d3db

SW certify (A vs B; seed swpf0)
root(A)=root(B)=57f0ffa07c3fd1830a59d254acf0c92bafa7825d053bdc9af839ccb4ba9ebe06 -> Certified

Receipt field glossary (one-liners)

kind chart (loop|family|feed|sw_pf) · steps/tau_points/z_points discretization · seed twist · phase_frac circle holonomy · root_sha256 Merkle root · file TSV source · rows,res_L1,res_Linf residuals. Aux: LEAVES -> path to <u>\t<leaf_hash> for first-difference forensics.
