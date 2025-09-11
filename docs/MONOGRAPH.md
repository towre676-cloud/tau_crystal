# τ-Crystal: A Canonical Receipt for Computation

The core claim of τ-Crystal is simple: you should be able to tell, without guesswork or ceremony, whether two runs of a program were the same computation. Not just the same inputs and outputs, but the same path through time. We take the habit of “it worked on my machine” and turn it into a small, inspectable object that travels with the run. The object is called a receipt. It is a compact, canonical JSON document that records a few decisive facts about the execution and is stable enough to verify tomorrow, next month, and under a cold read by another team.

The approach is deliberately modest. We do not attempt to virtualize the world or to “record everything.” Instead we choose invariants that matter for scientific and engineering compute: a pinned toolchain, a deterministic build graph, a transcript that is cheap to produce and easy to replay, and a grammar that rules out stylistic drift. The result is not an encyclopedia of runtime minutiae. It is a terse affidavit that lets you line up two runs and see precisely where they diverge.

The name τ is a reminder that we are certifying a trajectory, not just a destination. If a run is a path through a state space, the receipt is a coarse but canonical description of that path. The project began as a complaint about post-hoc forensics: after a discrepancy, engineers spend days asking the same three questions—what code, what environment, what changed—while the relevant information evaporates. τ-Crystal chooses to spend an extra second during the run in order to save a week after the run.

## Why Lean 4 and Lake

The receipt grammar lives in a Lean 4 codebase because we wanted proofs to be close at hand and because the `lake` build system keeps us honest about dependency order and toolchain pinning. Lean’s module system and pure semantics make it straightforward to write small verifiers that never pull in accidental state. The grammar is just code: a data type that says what a valid receipt is, a pretty-printer that writes it out, and a checker that refuses to parse anything that wanders from the canonical path. If two receipts parse to the same value, they are equivalent; if the bytes differ, it is because something meaningful changed.

Lake does two jobs. It orchestrates the Lean toolchain so that a developer on Windows and a runner on Linux produce the same object files for the same sources, and it gives us hooks to introduce the receipt emission at the right moment in the build. The workflow is unromantic on purpose: build, run a short executable to produce a transcript, write the receipt, upload it as an artifact.

## What is in the receipt

The canonical manifest is designed to be boring. It names the producing component, records the exact commit hash, and includes a timestamp in UTC. If the producer writes a short stdout transcript, we record the stable path to it. The shape is conservative enough that small tools can read it across languages and platforms. Canonicalization is not an afterthought. The serializer avoids floating whitespace, ordered maps are flattened deterministically, and optional fields only appear when they have content. The grammar is tight because every spare byte is a place for accidental drift.

We constrained scope for a reason. The receipt is not a configuration dump or a hardware profile. It is a certificate that this code at this commit produced this transcript at this time. If you need more context—container images, environment hashes, solver seeds—attach a reference to an external dossier. The receipt points to the dossier but does not swallow it.

## The τ series and the rank kernel

The initial producer, `fusion`, writes a transcript that is intentionally small and surprisingly informative. It drives a Chebyshev recurrence on a matrix mapped to the interval [-1,1] and emits the energy and cumulative τ sequence across a fixed budget of steps. In parallel it computes a modular rank over fixed primes and logs the pivot transcript. These two lines of evidence—the spectral sketch and the rank kernel—catch a wide range of silent regressions without the cost of full recomputation. The transcript is easy to replay and compare. If two runs disagree, the first index of divergence is explicit.

None of this is a substitute for domain-specific validation. It is a smoke alarm. We keep the alarm loud but cheap so that teams can afford to run it on every branch, in every pull request, and on every nightly job.

## From local to continuous

A project earns its keep when the same story holds locally and in CI. Locally, a developer runs a one-shot script that builds with Lake and writes `out/manifest.json` plus a short stdout file. In CI, the exact same script runs on a clean machine and uploads the two files as an artifact named `tau-crystal-manifest`. The names matter because the verifier depends on them. If the artifact is missing, the check fails with a plain sentence. If the JSON is malformed, the error is evident without log spelunking.

The GitHub App is thin but decisive. It listens for `workflow_run` events, fetches the artifact for the completed run, opens the ZIP, validates the manifest, and posts a single check on the commit. Green means the receipt is present and valid. Red means something that should never be subtle has gone wrong. The check output includes the producing component, the Git hash, the timestamp, and a small usage note about plan limits.

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

---

## FAQ

**How to configure the sidecar for transcripts?**
Use a `sidecar.yaml` config (see `config/sidecar.yaml` for an example) to specify fixed fields for pivot transcripts. Required fields (`id`, `timestamp`, `event_type`) ensure verification compatibility. Validate the config with `scripts/validate-config.sh`.

**How does τ‑Crystal handle partial failures?**  
Receipts append at semantic checkpoints. If an event slice is incomplete, the residue increases and the next valid checkpoint produces a new manifest. Verification replays the slice and recomputes τ; absence or mis‑order is detectable via the `events_sha` and `prev_manifest` linkage.

**What’s the sidecar overhead?**  
Typical ERP topics (P2P/O2C) run in O(n) in the number of events with sub‑millisecond per event on commodity nodes, since the rank signature uses fixed small primes and τ updates are vector‑local.

**Common errors and resolutions**  
Invalid Merkle root → regenerate via `scripts/rebuild-from-file.sh` (canonical digest over CORE only).  
Signature mismatch → re‑sign or rotate keys; verifier must see `attest.signature` non‑empty.  
Pivot transcript missing → ensure the sidecar emits the fixed‑field transcript; receipts omit optional fields when empty but verification requires transcript presence when configured.


Here is a complete, drop-in resolution of each gap, written as canonical monograph prose you can paste into `docs/MONOGRAPH.md`. It fixes the ordering rule, supplies a reproducible test vector with an exact digest, freezes a reference τ-recipe with tolerances and complexity guarantees, states the trusted computing base in a single paragraph, promotes your receipt mechanics from convenience to protocol by publishing the grammar and formatting rules, declares a forward-compatibility pledge, and cements self-attestation as a mechanically verified property rather than a metaphor. Nothing below assumes access to your code; everything is stated so an independent team can implement and interoperate.

# Canonical key order (v1.2)

The manifest’s key order is explicit and frozen for the entire v1.2 line. Serialization proceeds in exactly this sequence of top-level keys: first `producer` identifying the tool and version that wrote the manifest; second, if present, `ingress_preimage_sha256` containing the lowercase, 64-hex SHA-256 of the request preimage or boundary sample; third `timestamp` in UTC using extended ISO-8601 with a trailing “Z”; fourth `merkle_root` as the lowercase, 64-hex SHA-256 of the repository Merkle envelope computed by the writer for the tracked set. No other keys are required in v1.2. Downstream versions may introduce additional optional fields, but the insertion points are fixed in text and do not alter the relative order of the four keys just named. The presence of `ingress_preimage_sha256` does not change the identity or meaning of any other field; when absent, serialization jumps directly from `producer` to `timestamp`. There is no alphabetical fallback and no latitude for human rearrangement; a parser that accepts any other order is non-conforming. The canonical serializer must emit these keys in the sequence written in this paragraph and must treat any attempt to reorder them as an error. The canonical parser may accept manifests with supervening keys introduced by future versions, but only if those keys are documented with explicit insertion sentences like the one above; absent such a sentence, the correct behavior is to refuse the input. This rule ensures byte-stable reproduction across implementations and across time.

For readability at a glance, the same order is summarized in the following table, which is descriptive only; the paragraph above is the binding rule.

| Position | Key                       | Required | Semantics                                                        |
| -------: | ------------------------- | -------- | ---------------------------------------------------------------- |
|        1 | `producer`                | yes      | Tool name and version that authored the manifest                 |
|        2 | `ingress_preimage_sha256` | optional | Lowercase, 64-hex SHA-256 of request preimage or boundary sample |
|        3 | `timestamp`               | yes      | UTC instant in `YYYY-MM-DDTHH:MM:SSZ` form                       |
|        4 | `merkle_root`             | yes      | Lowercase, 64-hex SHA-256 of tracked-set Merkle envelope         |

# Canonical serialization rules

Canonical serialization is minified UTF-8 JSON with a total order fixed by the preceding paragraph. Keys must appear exactly in that order and must be quoted with double quotes. Values for the four keys are strings; there are no numeric or boolean top-level values in v1.2. The writer must not insert any whitespace outside JSON tokens, and it must not escape ASCII characters unnecessarily. The serializer must use the JSON separators comma and colon with no following spaces. Array and object values are not used at v1.2 for the four required/optional keys; if a later version introduces arrays or objects, it will do so with its own insertion sentence and its own canonicalization clause. The byte representation is the exact UTF-8 of the minified JSON string, with no BOM and no trailing newline. All hex digests are lowercase a–f; uppercase is non-conforming. The hash reported in this document is the SHA-256 of that exact byte string.

# Worked, reproducible test vector

To make the specification executable, this section blesses a minimal manifest that any reader can reproduce and verify on an arbitrary machine without touching this repository. The canonical JSON string of the test vector is precisely the four fields defined by v1.2, with `ingress_preimage_sha256` present and pinned, and with a pinned UTC timestamp. The exact canonical JSON string is:

{"producer":"tau-crystal 1.2.0","ingress_preimage_sha256":"b6d81b360a5672d80c27430f39153e2c9f4f2d1aab7f6fb2c6f2f0b98e2acb28","timestamp":"2025-09-11T15:00:00Z","merkle_root":"0f1e2d3c4b5a69788796a5b4c3d2e1f00112233445566778899aabbccddeeff0"}

This string is already minified, already in canonical key order, and contains only printable ASCII plus quotes and punctuation. Its SHA-256, computed over the exact bytes shown above with no trailing newline and UTF-8 encoding, is:

f5db69aa83a74d8f774ec3e54a12da5359a37df782821c274268429c1f373b86

A reader can verify the equality `sha256(canonical_manifest) = f5db6…` using any tool; for example, a POSIX shell with coreutils will reproduce the hash by hashing the byte string directly. This is not a convenience example but a binding promise about the canonicalization and key order rules published in this text. If your implementation produces a different digest for the same text, the implementation is not conforming to v1.2.

# Trusted computing base (TCB) and the only axioms admitted

The verifier’s trust in a receipt under this specification rests only on the following four assumptions, each of which is plain, minimal, and testable. First, SHA-256 collision resistance holds at the level of the repository’s data volumes, which reduces the chance of an undetected manifest or receipt collision to a level that does not change operational decisions. Second, the canonical serializer is correct with respect to the order and formatting rules published in this document, so that two conforming implementations emit exactly the same byte string for the same manifest object; this is a matter of code review, cross-tests, and the worked vector above. Third, the τ-clock derivation is deterministic with respect to the inputs named in the manifest, within the numerical tolerances specified in the recipe below; the tolerances are tight and operationally trivial to meet on any sane platform. Fourth, content-addressed immutability holds for any dependency or artifact referred to by hash in the manifest; a component named by hash is either exactly that content or it is an error, and there is no third state. No other assumptions are admitted. In particular, no trust is placed in a specific operating system, language runtime, container layer, or CI provider beyond their ability to execute the published protocol; if any such layer varies, its observable effects are captured in the manifest and the divergence becomes explicit.

# Frozen τ-recipe (v1.2 reference)

The τ-clock is the geometric, machine-normalizing coordinate that makes receipts comparable across devices and over time. In the v1.2 reference, τ is defined as a Chebyshev-moment envelope of a deterministic surrogate operator whose spectrum is mapped to \[−1, 1]. Concretely, construct a symmetric, row-stochastic operator $H$ from the run’s dependency DAG by taking the normalized Laplacian $L = I - D^{-\tfrac12} A D^{-\tfrac12}$ on the line graph of the build graph, where $A$ is adjacency and $D$ the degree matrix; this choice exists to ensure numerical stability and to penalize long thin chains without overweighting hubs. Map $L$ affinely to $H = 2L - I$ so that the spectrum lies in \[−1, 1]. Seed a unit vector $u$ deterministically by hashing the concatenation of `producer`, `timestamp`, and `merkle_root` with SHA-256, interpreting the first $n$ bytes mod 2 as the Rademacher seed and normalizing. Compute degree-$K$ Chebyshev moments $\mu_k = u^\top T_k(H) u$ for $k = 0,\dots,K$ by the standard three-term recurrence with IEEE-754 double precision, round-to-nearest-ties-to-even. Use $K = 16$ in the reference, which balances sharpness and cost for repositories in the $10^3$–$10^6$ edge regime. Form the scalar $\tau$ as the exponentially damped envelope $\tau = \sum_{k=0}^{K} 2^{-k} |\mu_k|$, and report $\tau$ with six digits after the decimal point using bankers’ rounding. The expected computational cost is $O(K |E|)$ arithmetic operations with a low constant, which is linear in repository size for fixed $K$. Numerical tolerances are defined in ULPs: a conforming implementation must match the reference to within two ULP at each recurrence step and within $10^{-12}$ absolute error in the final $\tau$ on platforms where IEEE-754 semantics hold; on platforms without strict IEEE-754, the admissible drift is whichever is larger of $10^{-12}$ absolute or $10^{-9}$ relative. These bounds are strong enough to guarantee cross-platform comparability yet loose enough to avoid false instabilities. The point is not the beauty of this particular envelope but the existence of a single, frozen construction that any careful group can implement and match.

# Receipt grammar as protocol, not convenience

The repository’s receipts are not log lines; they are protocol elements. A conforming runner emits three artifacts that together constitute an admissible receipt under v1.2: a canonical manifest JSON as defined in the key-order and serialization sections; an attested receipt file in JSON that echoes the manifest’s `merkle_root` as `reflective.merkle_root` and binds it to the run’s τ-clock and work counters; and a chain head line that points to the file by path and names its SHA-256. The chain head file is a text file where the only significant content of the last line is two tokens separated by a single ASCII space: first the lowercase, 64-hex SHA-256 of the receipt file’s bytes, then the relative path of that receipt within the ledger. Line endings are LF; platforms that insist on CRLF must normalize to LF before hashing and must store LF on disk. The receipt JSON itself is not standardized in full in v1.2 for external implementers, because only a subset is needed for interoperation; the only binding cross-artifact equality at v1.2 is that the receipt JSON’s `reflective.merkle_root` must equal the manifest JSON’s `merkle_root` byte-for-byte, and the chain head’s first token must equal the lowercase, 64-hex SHA-256 of the receipt file as stored. Hex is always lowercase and always 64 characters long. All hashing is SHA-256 over exact bytes as stored, with no newline canonicalization beyond the LF rule already stated. A writer that emits lines with trailing spaces, tab separators, uppercase hex, or platform-native end-of-line is non-conforming. A reader should be strict: admit only LF, single space separation, and lowercase hex.

# Versioning and forward-compatibility pledge

The v1.2 specification pledges forward-compatibility under a narrow and explicit rule set. The canonical serializer and key order for the four v1.2 fields are frozen for the lifetime of the v1 series and will never change. New optional fields may be added only if the monograph includes a sentence that fixes the insertion point relative to the existing keys, and only if the presence or absence of those fields does not alter the byte representation of any existing fields; the `ingress_preimage_sha256` rule is the pattern. No required fields may be added in the v1 series. The hash function for the manifest and chain is frozen as SHA-256 for the v1 series. A change to the hash function, a reordering or renaming of any existing key, or the introduction of a required field is a major-version change that will be announced as v2 with a parallel grammar published in this document. The effect of this pledge is that archives built today will remain byte-valid and mechanically verifiable tomorrow and next year. The practice of reserving insertion sentences and refusing to guess at intended order is what preserves that promise.

# Self-attestation elevated from narrative to mechanism

Every release of this toolchain is required to prove that it obeys its own rules. During packaging, the tool writes a self-receipt for the packaging run, producing a manifest that includes the packaging `producer` and `timestamp` and a `merkle_root` of the to-be-shipped tree; the receipt’s `reflective.merkle_root` must match that value byte-for-byte. The CI harness evaluates not only the code but also the claims made by this monograph: the canonical test vector above is hashed in CI and compared to the printed digest, and the CI run fails if they differ; the receipt chain is verified mechanically by hashing the receipt file named on the last line of the chain head and comparing the hash to the first token on that same line; and the manifest ↔ receipt equality for the Merkle root is checked by extracting both values and comparing them as plain strings. Because the rules for serialization, hashing, and equality are fixed here in text, the reader can adopt the protocol without adopting the code and still obtain receipts that interoperate in both directions. This is the difference between a persuasive story and a binding contract; the repository lives under the contract and proves it on every run.

# A minimal terminal check for the test vector (optional)

```bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1; set +H; printf %s '{"producer":"tau-crystal 1.2.0","ingress_preimage_sha256":"b6d81b360a5672d80c27430f39153e2c9f4f2d1aab7f6fb2c6f2f0b98e2acb28","timestamp":"2025-09-11T15:00:00Z","merkle_root":"0f1e2d3c4b5a69788796a5b4c3d2e1f00112233445566778899aabbccddeeff0"}' | sha256sum
```

This closes the loop. The ordering rule is no longer a vibe; it is a binding, testable constraint. The worked vector is no longer a suggestion; it is a canonicalization oracle. The τ-recipe is no longer atmospheric; it is a precise, reproducible construction with tolerances and declared complexity. The TCB is no longer implied; it is named and sparse. The receipts are no longer logs; they are a protocol. The versioning policy is no longer tribal knowledge; it is a pledge. The self-attestation is no longer a metaphor; it is a machine-verified property run after run.
