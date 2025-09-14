# τ-Crystal: A Canonical Receipt for Computation

The core claim of τ-Crystal is simple: you should be able to tell, without guesswork or ceremony, whether two runs of a program were the same computation. Not just the same inputs and outputs, but the same path through time. We take the habit of “it worked on my machine” and turn it into a small, inspectable object that travels with the run. The object is called a receipt. It is a compact, canonical JSON document that records a few decisive facts about the execution and is stable enough to verify tomorrow, next month, and under a cold read by another team.

The approach is deliberately modest. We do not attempt to virtualize the world or to “record everything.” Instead we choose invariants that matter for scientific and engineering compute: a pinned toolchain, a deterministic build graph, a transcript that is cheap to produce and easy to replay, and a grammar that rules out stylistic drift. The result is not an encyclopedia of runtime minutiae. It is a terse affidavit that lets you line up two runs and see precisely where they diverge.

The name τ is a reminder that we are certifying a trajectory, not just a destination. If a run is a path through a state space, the receipt is a coarse but canonical description of that path. The project began as a complaint about post-hoc forensics: after a discrepancy, engineers spend days asking the same three questions—what code, what environment, what changed—while the relevant information evaporates. τ-Crystal chooses to spend an extra second during the run in order to save a week after the run.

## Why Lean 4 and Lake
The receipt grammar lives in a Lean 4 codebase because we wanted proofs to be close at hand and because the lake build system keeps us honest about dependency order and toolchain pinning. Lean’s module system and pure semantics make it straightforward to write small verifiers that never pull in accidental state. The grammar is just code: a data type that says what a valid receipt is, a pretty-printer that writes it out, and a checker that refuses to parse anything that wanders from the canonical path. If two receipts parse to the same value, they are equivalent; if the bytes differ, it is because something meaningful changed.

Lake does two jobs. It orchestrates the Lean toolchain so that a developer on Windows and a runner on Linux produce the same object files for the same sources, and it gives us hooks to introduce the receipt emission at the right moment in the build. The workflow is unromantic on purpose: build, run a short executable to produce a transcript, write the receipt, upload it as an artifact.

## What is in the receipt
The canonical manifest is designed to be boring. It names the producing component, records the exact commit hash, and includes a timestamp in UTC. If the producer writes a short stdout transcript, we record the stable path to it. The shape is conservative enough that small tools can read it across languages and platforms. Canonicalization is not an afterthought. The serializer avoids floating whitespace, ordered maps are flattened deterministically, and optional fields only appear when they have content. The grammar is tight because every spare byte is a place for accidental drift.

We constrained scope for a reason. The receipt is not a configuration dump or a hardware profile. It is a certificate that this code at this commit produced this transcript at this time. If you need more context—container images, environment hashes, solver seeds—attach a reference to an external dossier. The receipt points to the dossier but does not swallow it.

## The τ series and the rank kernel
The initial producer, fusion, writes a transcript that is intentionally small and surprisingly informative. It drives a Chebyshev recurrence on a matrix mapped to the interval [-1,1] and emits the energy and cumulative τ sequence across a fixed budget of steps. In parallel it computes a modular rank over fixed primes and logs the pivot transcript. These two lines of evidence—the spectral sketch and the rank kernel—catch a wide range of silent regressions without the cost of full recomputation. The transcript is easy to replay and compare. If two runs disagree, the first index of divergence is explicit.

None of this is a substitute for domain-specific validation. It is a smoke alarm. We keep the alarm loud but cheap so that teams can afford to run it on every branch, in every pull request, and on every nightly job.

## From local to continuous
A project earns its keep when the same story holds locally and in CI. Locally, a developer runs a one-shot script that builds with Lake and writes out /manifest.json plus a short stdout file. In CI, the exact same script runs on a clean machine and uploads the two files as an artifact named tau-crystal-manifest. The names matter because the verifier depends on them. If the artifact is missing, the check fails with a plain sentence. If the JSON is malformed, the error is evident without log spelunking.

The GitHub App is thin but decisive. It listens for workflow_run events, fetches the artifact for the completed run, opens the ZIP, validates the manifest, and posts a single check on the commit. Green means the receipt is present and valid. Red means something that should never be subtle has gone wrong. The check output includes the producing component, the Git hash, the timestamp, and a small usage note about plan limits.

## Canonicalization as governance
People tolerate friction when they can feel the payoff, but they resent drift. The receipt grammar is our answer to drift. We favor determinism over convenience. When a field is optional, it is optional everywhere. When a serializer chooses a map order, it chooses it forever. When a new version is necessary, we version the grammar explicitly and keep the old checker available. The repository stays small because the grammar is small. The artifacts stay readable because the grammar is readable.

A good grammar enables a culture. Engineers stop arguing about where to put things because the grammar tells them where things go. Reviewers stop asking “is this the same as last week?” because the receipt comparison tells them instantly. The habit that remains is to ask “does this difference matter?” which is a human question that a machine can help you find.

## Security posture
The verifier never asks for secrets. It uses GitHub App authentication to read the artifact for the run that just finished, and it posts a check on the commit that triggered that run. The webhook HMAC keeps noise off the endpoint in production. In development we allow a stub mode to accelerate iteration, but the default posture is strict. The service keeps a tiny monthly counter to enforce plan limits; it does not store source code or raw artifacts beyond the lifetime of a single check. Privacy is a feature of the architecture, not a policy added at the end.

## Pricing that respects the work
We kept pricing simple because complexity is where distrust grows. The free tier is generous enough to be useful on a real project. The pro tier raises limits and unlocks organizational use. Entitlements come from GitHub Marketplace so there is no second identity to manage. The verifier checks whether the installation account has a current subscription and applies the appropriate limit. If the usage counter rolls over the monthly cap, the check turns into a polite nudge with a link back to the listing page. All of this happens in the same place engineers already live: a pull request.

## What happens when it fails
A failure should be a hint, not a riddle. The verifier writes a failure with a single line title and a paragraph that names the missing piece. If the artifact was not uploaded, it says so. If the manifest JSON is invalid, it says so. If the grammar check failed, it lists the fields that are wrong. These sentences are short because we would rather you fix the cause than read about it. The dashboards you already have—Actions logs and a diff of the receipt—carry the rest.

## How to extend the receipt
The grammar is intentionally open to narrow extensions. If a producer has a domain-specific transcript that belongs in the receipt, add a namespaced field with a stable schema and a parser that refuses ambiguity. Do not smuggle in free-form logs. Do not make the canonical parts of the receipt depend on execution environment or clock drift. If you must carry a reference to an external artifact store, keep the handle deterministic and treat the store as a cache, not a database of record.

This discipline means a lab or a company can carry their history forward without babysitting a zoo of ad hoc formats. A receipt from two years ago still parses. A receipt written tomorrow still compares to the one from last Tuesday. The set of valid receipts grows, but it does not meander.

## Why this matters
The point of reproducibility is not to pass an audit. It is to reduce the surface area of regret. When you keep a canonical receipt, you save the team from the weekly archaeology dig. When you keep the grammar tight, you save yourself from the next clever idea that turns into a maintenance burden. When you build the check into the place people already look, you save attention for work that only humans can do.

τ-Crystal is a polite constraint. It is a reminder to build the right kind of memory into the places where your code already lives. It gives you a receipt that reads the same in the morning as it did last night, and a green check that means what it says. In an era where everything is a platform, this is a tool that tries to be small on purpose.

## Road to adoption
Adoption is not a ceremony. Point your CI at the script, upload the artifact with the expected name, install the app, and watch the check appear. If you later want to turn the free plan into the pro plan, you do not change the code; you publish a Marketplace listing and remove the stub flag in your server’s configuration. The rest is culture work: write receipts as a matter of habit, treat the grammar as law, and enjoy the quiet that follows.

## A final word
This repository is intentionally strict and intentionally short. The work it does for you is cumulative. Every valid receipt you produce lowers the cost of the next investigation. Every time the check goes green without a second thought, you get a sliver of your day back. Software rarely pays you in small, regular dividends. τ-Crystal tries to.

MERKLE_ROOT: 41251899cddc5e32a22b498ee62f1458a2a517bc090349059fca60ec0337481c

STATUS: 2025-09-06T07:21:15Z • plan=FREE • receipt=unknown • hash=unknown

# τ‑Crystal Manifest

TAU_TANH2_SHA256: 8a692d462c8453c98fff3e8dd24ba2e0d55a5ba980d73537d61ef0dae80067c0

SOLITON_SHA256: be3faf88fd1d477ecfa7c13a558c9404a1bfa2a2e58b02b1f303ec68de54fe2b

This document tracks the verification lifecycle for this repository.

- `MERKLE_ROOT:` hash over all tracked files (plan + code)
- `STATUS:` most recent successful proof run and plan hash
- `attestation.txt:` lives in `.tau_ledger/attestation.txt`
- `receipts:` live in `.tau_ledger/receipts/`

Plan roots are defined in `.tau_plan_roots.env` and enforced in CI.
## sheaf (v1)

digest: 8faa7c4b077e817e0a5f266f7281ef5787037e859559606a0c79e802004b8d1f

## timefold (v1)

id: tf-20250914T022521Z
label: initial
utc: 20250914T022521Z
archive: tf-20250914T022521Z.tar.gz
sha256: 64f58a257fe90657680487de866ad37a765fcfc3d3fdafe9a5f5f67653da2450
bytes: 5491
files: 4

## qr_witness (v1)

witness_path: .tau_ledger/CHAIN
witness_sha256: 46ba5b15905fb11547ea79e53c9206af232beff595e5a3cc3b369db62c24e9c9
svg_path: .tau_ledger/qr/qr-witness.svg

## entropy (v1)

id: entv1-20250914T023136Z
head_change: changed
timefold_bytes: 0
entropy_sha256: 3e0ee0df760df0f5cb7696a18acfbd38664c6b7f1f3b8a30fdcac50bf1cbc622

## interference (v1)

svg: .tau_ledger/interf/interference.svg
sha256: 8fa8c97ea6c0149efe3df0a2b41e84eb78b2151ad2cfd526ae0716a589e3d39d

## signature_ring (v1)

id: ringv1-20250914T023849Z
sha256: 59e47883e182f4fad3ca156ef097d2f9bfe7136b1a786fc7e55b15c5bf16e688

## federation (v1)

- id: hello.receipt
  url: url
  sha256: 98db61415ffcc4dac893faf209c40265b60357a60abb02bf62011a7fb12dd419

## policy_gate (v1)

id: policyv1-20250914T025734Z
utc: 20250914T025734Z
%s
checks_passed: 3
checks_failed: 1
report: .tau_ledger/gates/report.20250914T025733Z.txt
report_sha256: a34c23d7fee194aa256fc23c23eac740dad61ff9dabee9881236b109e2481538

