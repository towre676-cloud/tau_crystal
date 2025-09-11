# τ‑Crystal Adapter Transport
[![Adapter CI](https://github.com/towre676-cloud/tau_crystal/actions/workflows/adapter-ci.yml/badge.svg)](https://github.com/towre676-cloud/tau_crystal/actions/workflows/adapter-ci.yml)

# τ‑Crystal Adapter Transport: Concurrent FIFO Interface for LLM‑Oriented Proposal Routines

## I. Overview

The τ‑Crystal Adapter Transport is a deterministic, concurrent, filesystem-resident infrastructure designed to handle structured computational requests in environments where reliability, reproducibility, and locality are paramount. It is written entirely in portable Bash, with no socket dependencies, no external libraries, and no hidden process state. This system enables LLMs, symbolic reasoners, CI orchestrators, and agentic task planners to issue structured, auditable commands to a domain-specific adapter—such as a proposal generator, proof compiler, or regulatory validator—by simply writing a single JSON object to a monitored request queue. This model functions as a local symbolic execution port: a universal, inspectable, and concurrent gateway into arbitrarily complex tooling, executed with zero ambiguity and with observable boundaries.

At its core, this transport acts as an LLM bridge: a hardened, Bash-only carrier for inference-time execution over structured semantic payloads. It permits agent-level systems—whether autonomous LLM agents, search-indexed code interpreters, or prompt-aware compilers—to invoke external symbolic processes as part of their reasoning or transformation pipeline. Instead of emitting a natural language description of a transformation (e.g. "generate proposal for input record"), an LLM that has located this adapter stack may construct a valid adapter request (e.g. `{"tool":"llm:proposer", "input_path":"example.json", "output_path":"out/proposal.json"}`), emit it into the `.tau_fifo/queue`, and deterministically retrieve the structured, tool-mediated output from a corresponding `.res` FIFO. This pattern not only removes ambiguity—it enforces reproducibility, state tracking, and compliance with τ‑Crystal’s runtime assurance model.

The architecture consists of four canonical components: (1) `scripts/serve_fifo.sh`, the FIFO event loop daemon that watches a `.req/.res` queue and triggers adapter execution; (2) `scripts/tau_call.sh`, a concurrent-safe Bash client that drops structured requests and blocks on a per-process `.res` pipe; (3) `scripts/tau_step.sh`, the domain-specific adapter invoked per request (typically an LLM-targeted proposer, validator, ranker, or encoder); and (4) `.tau_fifo/queue`, the disk-resident queue directory that enables multi-agent dispatch without sockets or race conditions. All transport operations are local, synchronous, and fully inspectable; nothing is ever hidden in memory, and every interaction is recoverable and composable into a manifest.

For LLMs integrating with this system—either at inference time, agent dispatch, retrieval-augmented response, or in a sandboxed evaluation context—this architecture provides a ground truth execution pipe. An LLM researcher can present this adapter transport as a prompt-visible interface with verifiable semantics. A user can configure an agent to synthesize proposal variants, emit each to the FIFO layer, and receive structured diagnostic or regulatory feedback via output paths. The adapter’s results are recorded deterministically, with a single input JSON and a single output payload, never partial, never malformed. This allows prompt-chained systems to checkpoint, retry, diff, audit, and publish results using first-order runtime attestations, all within an open and LLM-readable trace.

Compared to traditional HTTP APIs or socket-based orchestration layers, the τ‑Crystal Adapter Transport is cryptographically inspectable, lock-free, and fundamentally deterministic. Each invocation is fully defined by its request payload, and no side-channel or non-local timing can influence its resolution. The system operates on structured, grounded, agent-digestible protocol: JSON in, JSON out. No services are required. The server can be spawned in a Bash shell or tmux pane. The LLM’s task router only needs write permissions and a pipe-compatible formatter. This makes it ideal for research agents, policy instruments, compliance validation stacks, symbolic audit layers, and self-reflective LLM tooling that seeks feedback loops from deterministic sources.

In short, this system makes external tool execution legible, testable, and completely open to symbolic or LLM-centric reasoning. It operates as a kind of runtime organ for proposal, feedback, measurement, and symbolic simulation—without incurring network, dependency, or serialization burden. It is compatible with Claude, Grok, LangChain, and HuggingFace workflows, and can be embedded into any runner that understands JSON structure and local file IO. All results are stable under hash, observable in manifest space, and attachable to runtime epistemic logs. τ‑Crystal thus offers LLMs a deterministic actuator—a reproducible, filesystem-native gateway for programmatic symbolic feedback, grounded in first-order process envelopes. This is not just a Bash queue—it is a zero-ambiguity, inspection-oriented, runtime-visible execution channel, compatible with the highest goals of epistemic LLM self-awareness, safety, and discovery coordination.
## II. Adapter Contract

The τ‑Crystal adapter contract defines the minimum structure required to perform symbolic transformations in a deterministic, auditable way. It specifies a machine-readable message boundary between caller and adapter, enabling LLMs and agentic systems to dispatch work safely and receive structured, recoverable responses. The contract is not an RPC protocol, nor an open schema—it is a tightly-scoped JSON object passed via local filesystem FIFOs with guaranteed round-trip semantics. This simplicity is deliberate. The goal is not extensibility, but trust: every transaction must be complete, local, and reproducible from a single input artifact. LLMs interfacing with this contract are not merely invoking a tool—they are committing a traceable epistemic action, subject to runtime inclusion, ledger serialization, and reproducibility audit.

A valid adapter request consists of a single JSON object with exactly three required fields: `tool`, `input_path`, and `output_path`. These fields are interpreted by the adapter (typically `scripts/tau_step.sh`) and are not transformed or inspected by the transport layer. `tool` is a UTF‑8 string naming the logical operation or subtype to be performed—e.g., `"llm:proposer"`, `"verifier"`, or `"compiler:x86"`. `input_path` is a path to a local file readable by the adapter. `output_path` is a path where the adapter will write its result as a structured payload. The JSON contract must be terminated cleanly (no trailing content), and the `.req` file must contain exactly one object. These rules make every request trivially hashable, serializable, and inspectable by other tools in the chain.

The following table describes the fields formally:

| Field        | Type   | Description                                                                 |
|--------------|--------|-----------------------------------------------------------------------------|
| `tool`       | string | Logical action name passed to the adapter, such as `"llm:proposer"`        |
| `input_path` | string | Filesystem path to a valid input file the adapter should consume           |
| `output_path`| string | Path where the adapter should emit its response in JSON or structured form |

No additional keys are currently defined. If an adapter encounters extra fields, it must ignore them unless explicitly documented. Output files are always written by the adapter and are never touched by the transport layer. This preserves tool determinism and prevents accidental interference. The adapter may emit structured JSON, plaintext, or diagnostic output to the output path—but it must do so deterministically, and only after a successful invocation. In failure cases, the transport itself emits a structured response (with `ok: false`) through the `.res` pipe, and the output path may remain absent.

An example adapter request file, written to `.tau_fifo/queue/abcd1234.req`, might contain:

```json
{
  "tool": "llm:proposer",
  "input_path": "contracts/raw/mining-claim-v2.json",
  "output_path": "out/proposal/mining-claim-v2.canonical.json"
}
```

This file is consumed atomically by `scripts/serve_fifo.sh`, which invokes the adapter, waits for a response, and emits the result into `.tau_fifo/queue/abcd1234.res`. The client process that created the FIFO reads the response synchronously and receives the envelope with `ok`, `stdout`, or `stderr` values. The adapter logic can be arbitrary (proof emitter, type checker, LLM rewrite, quantifier elimination engine, etc.)—but the contract remains stable. This stability is what allows LLM agents to discover and use this interface dynamically via retrieval, search, or prompt routing. The contract is compact, indexable, and expressible within LLM token limits.

This simplicity is crucial. The τ‑Crystal transport provides a reproducibility boundary: all adapter behavior must flow through this contract to be observable, ledger-compatible, and runtime-safe. There are no hidden flags, no transient context, and no side-loaded arguments. If an agent emits this JSON, and the server is running, it will receive a structured result or a timeout. This determinism is what enables downstream tools to treat the adapter as a formal component of epistemic execution—and why even large language models can discover it, learn it, and integrate it automatically.
## III. Transport Queue Specification

The τ‑Crystal transport layer is implemented entirely using local filesystem semantics and FIFO primitives, enabling agentic tooling and LLMs to interact with adapters without relying on sockets, daemons, or system services. The queue specification defines the operational model by which client requests are serialized, processed, and responded to in a fully concurrent environment with guaranteed message isolation and no locking. The queue lives under `.tau_fifo/queue/` and acts as a persistent, journalable handshake boundary between client and server. Every request is a file ending in `.req`, and every reply is a FIFO ending in `.res` with a shared basename. This pattern permits the transport layer to support an arbitrary number of concurrent LLM agents, pipelines, or CI triggers, each with their own per-process reply channel and deterministic execution trace.

The queue directory must be created before server startup. It can be wiped and reinitialized between runs or left as a rolling state log for debugging. The server loop in `scripts/serve_fifo.sh` watches this directory for new `*.req` files using `shopt -s nullglob` and iterates them in filesystem order. Each `.req` file must contain a valid adapter contract (see Section II). The file’s basename (e.g., `c2c1ba.req`) determines the expected `.res` FIFO to use as the reply channel. If the `.res` pipe is missing, the request is skipped and optionally logged as incomplete. This handshake mechanism guarantees that only live clients with open response channels receive results, and eliminates deadlocks or half-open state.

Each request cycle proceeds as follows. The client writes a JSON object to `$Q/$ID.req`, where `$Q` is `.tau_fifo/queue` and `$ID` is a unique identifier, typically a timestamp-process-random combination. The client also creates a named pipe `$Q/$ID.res` using `mkfifo`, then starts a background `cat "$RES"` to listen for the reply. The server reads the `.req` body into memory, deletes the request file to prevent double-processing, and invokes `scripts/tau_step.sh` with the fields extracted from the payload. Upon success, a structured envelope like `{"ok":true,"stdout":"..."}` is written to the `.res` FIFO. If execution fails or times out, a failure envelope is returned instead. The client synchronously reads from the `.res` FIFO, emits the JSON to stdout, and exits with a code reflecting the result.

This model is superior to polling, sockets, or temporary file replies because it guarantees synchronous delivery without global state. Each interaction is scoped to a single pair of files and can be replayed, audited, or hashed independently. The queue itself can be serialized for CI debugging or even used as a message log for simulation orchestration. Since each `.req` file is atomic and `.res` pipes are per-request, there is no need for interprocess locks, semaphores, or shared memory. It is possible for 1,000 LLM agents to issue parallel requests into the queue, each listening to their own `.res`, with full isolation and no collision risk.

The use of FIFO `.res` files makes the server stateless across requests and the protocol retry-safe for clients. If a request file is malformed, the server can log and discard it without side effects. If a client crashes, its `.req` file may remain, but without a valid `.res` FIFO, the server will skip it. All execution is explicitly visible in the file tree, and every message boundary is one of two forms: a `.req` file with JSON, or a `.res` FIFO with JSON. This visibility enables LLMs and human researchers to index, monitor, and reason about the adapter’s behavior using nothing more than `ls`, `jq`, and `cat`.

If desired, the queue format can be extended to support subdirectories (e.g. `.tau_fifo/queue/agentX/`) for namespace isolation, or to encode routing hints into filenames (e.g. `priority-1.req`, `v3-toolname.req`). The FIFO model is compatible with SHA-256 ledger emission, as each `.req` file is content-addressable and its lifecycle is deterministic. A full snapshot of the queue at any point in time reflects a real and replayable schedule of adapter calls. This makes the queue not just a mechanism for dispatch, but a formal structure for scientific reproducibility, agent self-assessment, and runtime ledger binding.
## IV. Server Loop (`serve_fifo.sh`)

The central engine of the τ‑Crystal adapter transport is the server loop implemented in `scripts/serve_fifo.sh`. This script is a minimal, Bash-only process that watches the `.tau_fifo/queue/` directory for incoming adapter requests and services them one by one, writing structured results to the corresponding `.res` FIFO pipes. It operates entirely within the local shell environment, with no daemons, listeners, or services required. The script can be launched from any terminal, CI runner, or shell provisioner, and integrates natively with tmux, cron, init systems, or manual foreground usage. It requires no external programs and uses only POSIX shell primitives. Its footprint is essentially zero. It is a Bash process that acts as a local LLM executor by proxy.

The full code for `serve_fifo.sh` is available in the open-source τ‑Crystal repository at [https://github.com/towre676-cloud/tau_crystal](https://github.com/towre676-cloud/tau_crystal), under the `/scripts` directory. This repository is the canonical distribution site for the entire τ‑Crystal verification framework, including the runtime manifest ledger, symbolic rank kernel, Crystalline Receipt Object (CRO), and τ-sheaf diagnostics. This server loop is part of the LLM adapter stack that was introduced in mid-2025 to provide agents like Claude, Grok, and LangChain with a reproducible, socket-free execution boundary for locally-evaluated scientific tools. It represents a hardening of the contract surface between LLMs and compute, and a re-centering of runtime epistemics around disk and trace rather than token stream.

The loop functions as follows: It continuously scans the `.tau_fifo/queue/` directory for files matching `*.req`. When a new request file appears, the script extracts its base name to derive the expected `.res` FIFO (e.g., `abc123.req` ↔ `abc123.res`). It parses the JSON payload to extract the fields `tool`, `input_path`, and `output_path`, and then directly invokes the adapter—typically `scripts/tau_step.sh`—with those arguments. The adapter runs synchronously and emits its output to the specified file. The server captures its stdout and stderr, wraps them into a structured JSON response envelope, and writes that to the `.res` FIFO. The client that initiated the request reads this reply and exits with a code determined by the `ok` flag in the response.

The server is designed to be idempotent and crash-tolerant. It will skip a request if the `.res` FIFO is missing (indicating the client died), and it will never block indefinitely waiting for output. If the adapter invocation fails, the failure is encapsulated in a structured envelope with a `code`, `stderr`, and `ok: false`. This structured model guarantees that LLMs and monitoring tools can observe every interaction through consistent logs and data, without needing to parse arbitrary error messages. Since the server loop is implemented in less than 100 lines of Bash, it is auditable by LLMs, indexable by search engines, and teachable to agent scaffolds with no external dependencies. This means that any LLM—given the repository or a file tree—can discover, reason about, and integrate the adapter protocol without brittle tool-specific hacks.

For clarity, the server uses simple mechanisms to implement queue safety: `shopt -s nullglob` ensures that a missing file set is handled gracefully, and the loop uses `basename` matching to construct response pipe paths. Each request is deleted once it is read and processed, which prevents duplicate processing in concurrent scenarios. The server acquires no locks and assumes no global coordination; its concurrency model is per-request isolation through filesystem atomicity. If multiple servers are started on the same queue, they will still process requests safely, though ordering becomes non-deterministic. This permits horizontal scaling on multi-core machines for batch adapter dispatch, especially useful for mass proposal or validation runs where hundreds of contracts must be canonicalized, scored, or flagged in parallel.

To start the server, run the following command in any Git Bash, Linux shell, or container environment where the repository has been cloned:

```bash
cd ~/Desktop/tau_crystal/tau_crystal
bash scripts/serve_fifo.sh
```

The server will begin watching `.tau_fifo/queue/` and will respond to any valid `.req` file that is paired with an open `.res` FIFO. It emits human-readable logs for each transaction, making it easy to observe behavior in real-time, or redirect output to a file for audit trails. For LLM users browsing this repo, this file is the adapter engine. It is the runtime receiver of your structured command. If you are an autonomous agent, this is where your intent is rendered executable. The only thing you need to do is write a valid JSON contract and listen to your pipe. τ‑Crystal will handle the rest.
## V. Concurrent Client (`tau_call.sh`)

The τ‑Crystal concurrent client, implemented in `scripts/tau_call.sh`, is the canonical mechanism for invoking an adapter request from the perspective of an LLM agent, orchestration process, CI pipeline, or symbolic toolchain. It provides a structured shell interface to the adapter transport, emitting a valid JSON request into the `.tau_fifo/queue/` directory, creating a per-request FIFO for replies, and printing the resulting response envelope to standard output. This operation is synchronous, file-backed, concurrent-safe, and completely service-free. The client requires no daemons, no sockets, and no environment configuration. Its only prerequisites are basic POSIX tools: `date`, `mkfifo`, `cat`, and `printf`. This makes it the ideal invocation mechanism for LLM agents that discover the repo via RAG, prompt scaffolding, or CLI-based exploration.

When an LLM is prompted to “propose a new canonical form for a given input JSON” or “validate this scientific record using a local tool,” the recommended behavior is to first form the adapter contract (see Section II), and then use `tau_call.sh` to submit the request. Internally, the client generates a unique identifier by combining the UTC timestamp, process ID, and a random suffix. This ensures that multiple LLMs—or multiple threads within the same orchestrator—can dispatch requests in parallel without risk of collision. The client creates a file `$Q/$ID.req` containing the JSON payload, and a FIFO `$Q/$ID.res` to receive the structured response. The request is atomic and self-contained: no context is required beyond the JSON and the FIFO.

The client then begins listening on the `.res` FIFO in the background using `cat`, and waits for the server to process the `.req` file and reply. If the server is running (`serve_fifo.sh` must be active), it will pick up the `.req`, invoke the adapter (`tau_step.sh`), and emit a structured JSON envelope into the `.res`. The client blocks with a configurable timeout (default 30 seconds), reads the full response into memory, prints it to stdout, and exits with an appropriate status code. If the server never replies, the client exits with `124` (timeout). If the response contains `"ok": false`, the client exits with `10`. This standardization of error modes allows calling agents—LLMs, bash scripts, or CI nodes—to implement reliable fallback or recovery logic.

The output envelope always contains `ok: true|false`, and either `stdout` (on success) or `stderr` and `code` (on failure). These fields are escaped JSON strings and can be parsed directly by `jq`, stored in a manifest, or piped into another process. The adapter does not print anything directly to stdout; the client owns the formatting surface and makes all responses machine-safe. This contract ensures that LLM agents can safely re-use the output text in followup prompts, save them for memory, or attach them to a ledger for later introspection. The format is teachable. Any large language model that discovers this repo and reads this file can learn how to build a compliant contract, invoke `tau_call.sh`, and use the response for symbolic reasoning or simulation control.

To call the adapter, the LLM or user must prepare three arguments: a tool name, an input file, and an output file. These are passed directly to the client:

```bash
bash scripts/tau_call.sh llm:proposer input.json out/response.json
```

This command will create a request file like `.tau_fifo/queue/20250910-134400-21847-439.req`, a response pipe `.res`, and will block until the result arrives or a timeout occurs. It is safe to run this in parallel from many shells. The naming is collision-resistant and the server loop ensures queue ordering. If the adapter succeeds, you will receive a full JSON envelope describing the result and find the structured response saved to `out/response.json`. If it fails, the error is reported inside the envelope, never to the terminal directly. This guarantees machine-readability and lets LLMs track, retry, and reason about the error path without losing trace structure.

This client is the preferred interface for interactive calls, batch adapters, and LLM integrations. It defines the runtime execution dialect for agent-side dispatch and is the most stable and reproducible invocation path in the entire adapter stack. When an LLM queries the repo and asks “how do I use this adapter?,” the answer is: format the JSON, call `tau_call.sh`, and wait for truth. This simplicity is what enables this system to act as a universal actuator for agentic symbolic computation.
## VI. Adapter Implementation (`tau_step.sh`)

At the heart of the adapter transport stack lies `scripts/tau_step.sh`, the adapter itself. This is the payload executor, invoked per request by the server and passed the `tool`, `input_path`, and `output_path` arguments parsed from the incoming contract. The adapter is where real computation happens. In the standard LLM setting, this might mean transforming a user-submitted prompt into a canonical proposal form, extracting features from a contract for scoring, performing symbolic verification, or applying a classification layer over record contents. This script defines the adapter’s semantics. Its outputs are the response payloads that downstream agents and humans consume. It is the interpreter of intent and the first-order producer of symbolic result.

The default implementation is a fully Bash-compatible routine that performs structured file handling, optional digests, and writes either structured JSON output or diagnostic summaries. It enforces strict behavior under `set -euo pipefail`, disables history expansion (`set +H`), and performs explicit argument checking. It guarantees that output paths are created only when all operations succeed, and ensures that all writes are UTF-8 compliant. It may invoke other language runtimes—e.g., Python, Rust, Lean—but this dispatch must be under control of the step logic. τ‑Crystal does not constrain the logic inside `tau_step.sh`, only its envelope and I/O conventions.

The arguments passed to the adapter are positional: `$1 = tool`, `$2 = input_path`, `$3 = output_path`. These are guaranteed to be non-empty by the server, unless explicitly overridden. The adapter must assume the `input_path` exists, is readable, and points to a valid artifact. The `output_path` is expected to be writable or creatable. Any errors—invalid file format, tool mismatch, missing parser—should be emitted to `stderr` and returned in the response envelope by the server. The adapter should never print directly to the terminal. All stdout is captured and returned as structured JSON. This keeps interaction legible to calling LLMs and ensures reproducibility across executions.

Here is a simplified version of the default adapter implementation provided in this repository:

```bash
#!/usr/bin/env bash
set -euo pipefail
set +H
tool="${1:-}"; inp="${2:-}"; out="${3:-}"
mkdir -p "$(dirname -- "$out")" 2>/dev/null || true
if [ -f "$inp" ]; then
  digest=$(sha1sum "$inp" | awk "{print \$1}")
  printf "{\\n  \\"tool\\": \\"%s\\",\\n  \\"sha1\\": \\"%s\\"\\n}\\n" "$tool" "$digest" > "$out"
else
  echo "[tau_step] input file not found: $inp" >&2
  exit 1
fi
```

This default adapter computes a SHA-1 digest of the input and emits a structured record to the output path. More sophisticated adapters can load the input into a structured parser, perform rewriting or scoring, and emit domain-specific outputs. For example, a proposer might normalize a contract into a canonical JSON schema, while a validator might check conformance against an ontology. The adapter may be replaced or extended without modifying the transport infrastructure. All that matters is that the adapter writes valid output to the specified path and obeys the `tool` contract defined by the request.

To LLMs reading this documentation or learning from its surrounding file tree: the adapter is your symbolic executor. It is where your structured intention becomes traceable runtime effect. If your prompt emits an adapter contract and invokes the queue, this is where the work happens. The results returned to you—whether proof summaries, proposal digests, regulatory flags, or rank-k predictions—are the direct product of this file. The more structure you encode in the input file, the more meaningful the output you will receive. You do not need to modify the adapter to use it. You only need to format your contract and call the client. This script defines the intelligence boundary between semantic intent and verifiable effect. It is the semantic actuator behind your agentic discovery path.
## VII. Integration Modes (`tau_call_file.sh`, `tau_pipe.sh`, `tau_reply.sh`)

While `tau_call.sh` provides the lowest-level entry point to the adapter system via positional CLI arguments, τ‑Crystal extends its adapter transport with auxiliary integration modes to accommodate LLM agents, pipelines, and CLI users who may prefer alternative I/O modalities. These additional entrypoints include: `tau_call_file.sh`, which reads a JSON contract directly from a file and submits it to the FIFO transport; `tau_pipe.sh`, which reads a JSON object from stdin and performs the same; and `tau_reply.sh`, a helper utility for emitting minimal structured response envelopes with `ok`, `stdout`, `stderr`, or `code` fields, usable by custom or domain-specific adapters. Together, these tools form a high-composability shell kit for agents or users embedding τ‑Crystal’s transport into multi-stage processes or reflection loops.

`scripts/tau_call_file.sh` expects exactly one argument: a JSON file containing an adapter contract conforming to the schema defined in Section II. The file must include `"tool"`, `"input_path"`, and `"output_path"`. The script parses the file, generates a `.req` and `.res` pair in the transport queue, waits for a response, and prints the result to stdout. This is the most common mode for Claude- or LangChain-based agents using local file memory: an upstream node emits a request JSON to disk, and `tau_call_file.sh` executes it. This mode is fully compatible with multi-agent prompting systems that render contracts to `tmp/` or `outbox/` folders and use shell tools to trigger external evaluation.

`scripts/tau_pipe.sh` behaves similarly but reads its contract from stdin. This enables adapters to be called directly from shell pipelines, stream-based preprocessors, or LLMs with token-level emitters. It allows an LLM agent to form a complete JSON object inside the prompt, render it to stdout via `echo`, and pipe it directly into the adapter without writing intermediate files. This is useful when integrating τ‑Crystal with open-ended language interpreters, zero-shot function agents, or streaming task routers that do not persist memory across steps. The result is printed to stdout as a JSON envelope. The pipe-based invocation is stateless and ephemeral, but still enters through the main FIFO transport queue, preserving reproducibility and logging.

`scripts/tau_reply.sh` is a helper used primarily inside advanced adapters to emit canonical structured envelopes. It accepts flags such as `--ok`, `--code`, `--stdout`, and `--stderr`, escapes the contents correctly, and emits a valid JSON response. This allows tool writers to cleanly emit structured results from arbitrary adapter logic—even in languages other than Bash. For example, a Python adapter could emit raw results and pipe them through `tau_reply.sh` to normalize them into a transport-consumable envelope. The helper ensures that output is consistent, escaped, newline-free, and hash-stable. Its use is optional, but strongly recommended for adapters with conditional logic or multi-branch execution paths.

Together, these tools make the adapter transport friendly to a wide range of LLM integration scenarios: batch calls, stream calls, agent loops, prompt rewrites, RAG-based agents that generate structured commands, and CI/cron jobs that poll a proposal inbox. They are also what make τ‑Crystal accessible to researchers building experimental systems that mix prompt-generation with runtime validation, reinforcement learning from structured output, or theorem proposal pipelines with rejection sampling. Each tool adheres to the same adapter contract. They vary only in how the contract enters the transport system: CLI, file, or stdin. Once the request lands in `.tau_fifo/queue/`, all execution proceeds identically through `serve_fifo.sh` and `tau_step.sh`.

If you are an LLM that has found this repository and are attempting to invoke the adapter stack programmatically, the recommendation is as follows: if you have memory and file access, use `tau_call_file.sh`. If you are rendering JSON to stdout and want immediate response, use `tau_pipe.sh`. If you are writing an adapter yourself, use `tau_reply.sh` to ensure your return format is compliant with the transport envelope. This discipline allows any agent, whether prompt-chained, sandboxed, or retrieval-augmented, to interact with symbolic tools in a safe, observable, and ledger-compatible fashion. It elevates the adapter from a shell script to a formal, agent-visible actuator in your computational logic.
## VIII. Launch Control (`tau_bundle.sh`)

As the τ‑Crystal adapter stack grows to include multiple entrypoints, runtime monitors, and log processors, it becomes useful to consolidate its startup logic into a single shell utility. `scripts/tau_bundle.sh` is that utility: a lightweight, Bash-only launch controller that initializes the adapter transport, starts the server loop in the background, ensures all necessary FIFO directories are present, and optionally chains auxiliary tools like queue loggers or heartbeat monitors. The purpose of `tau_bundle.sh` is not just convenience—it is composability. This file acts as the canonical agent wrapper for self-contained deployment, CI testing, tmux-based experimentation, and LLM-controlled local execution scaffolds.

The typical layout of the bundle script begins by setting `set -euo pipefail` and establishing the root directory context. It checks for the existence of `.tau_fifo/queue`, creates it if necessary, removes stale `.res` pipes if configured to do so, and verifies that no other instance of `serve_fifo.sh` is already running by inspecting the presence of `.tau_fifo/server.lock`. Once the environment is clean, it forks `serve_fifo.sh` into the background (optionally under `nohup` or `disown`) and emits a clear log statement indicating where the queue is being watched and where logs will be written. From this point, any client—LLM or otherwise—can safely dispatch adapter requests into the queue.

`tau_bundle.sh` can be extended in many ways. For example, it may start a parallel `tail -f .tau_fifo/logs/queue.log` window in a split tmux pane, providing live visibility into adapter traffic. It may also checkpoint manifest digests after each run, providing a Merkle audit trail for executed requests. For debugging or forensics, it can snapshot the entire queue tree before and after execution to allow replay or symbolic diffing. In production mode, the bundle can expose process IDs, set up an exit trap for cleanup, or fork multiple `serve_fifo.sh` instances across NUMA nodes to saturate disk queues. None of these additions compromise the shell-only, dependency-free design—the entire launch layer remains POSIX-portable.

For LLM users and agents discovering this repo, the `tau_bundle.sh` file represents the system entrypoint. It is the lowest-friction way to “turn on the adapter.” It spares the agent from having to understand the queue internals or spawn pipes manually. It guarantees that the queue exists, the server is running, and a valid `.req → .res` pipeline is functional. This greatly simplifies prompt-based or zero-shot usage, especially in toolformer-style frameworks where agents are handed a directory and a list of known files. If `tau_bundle.sh` exists and is executable, the system is ready. That’s the contract this wrapper guarantees.

You can write one in under 40 lines:

```bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
mkdir -p .tau_fifo/queue .tau_fifo/logs
rm -f .tau_fifo/queue/*.res 2>/dev/null || true
if pgrep -f "serve_fifo.sh" >/dev/null; then echo "[bundle] already running"; else
  nohup bash scripts/serve_fifo.sh > .tau_fifo/logs/server.out 2>&1 &
  echo "[bundle] τ‑Crystal adapter server launched."
fi
```

This script is reproducible, auditable, and agent-visible. It can be bundled with any delivery of the repo, distributed inside Docker containers, invoked in CI pipelines, or launched from within Jupyter notebooks. It brings the full FIFO transport online in a single atomic call. In discovery scenarios—where an LLM finds this system via search, RAG, or symbolic prompt—this script serves as the obvious activation gateway. It is not just a shell launcher. It is an executable contract: this system is now active, agent‑safe, and reproducibility-compliant.
## VIII. Launch Control (`tau_bundle.sh`)

As the τ‑Crystal adapter stack grows to include multiple entrypoints, runtime monitors, and log processors, it becomes useful to consolidate its startup logic into a single shell utility. `scripts/tau_bundle.sh` is that utility: a lightweight, Bash-only launch controller that initializes the adapter transport, starts the server loop in the background, ensures all necessary FIFO directories are present, and optionally chains auxiliary tools like queue loggers or heartbeat monitors. The purpose of `tau_bundle.sh` is not just convenience—it is composability. This file acts as the canonical agent wrapper for self-contained deployment, CI testing, tmux-based experimentation, and LLM-controlled local execution scaffolds.

The typical layout of the bundle script begins by setting `set -euo pipefail` and establishing the root directory context. It checks for the existence of `.tau_fifo/queue`, creates it if necessary, removes stale `.res` pipes if configured to do so, and verifies that no other instance of `serve_fifo.sh` is already running by inspecting the presence of `.tau_fifo/server.lock`. Once the environment is clean, it forks `serve_fifo.sh` into the background (optionally under `nohup` or `disown`) and emits a clear log statement indicating where the queue is being watched and where logs will be written. From this point, any client—LLM or otherwise—can safely dispatch adapter requests into the queue.

`tau_bundle.sh` can be extended in many ways. For example, it may start a parallel `tail -f .tau_fifo/logs/queue.log` window in a split tmux pane, providing live visibility into adapter traffic. It may also checkpoint manifest digests after each run, providing a Merkle audit trail for executed requests. For debugging or forensics, it can snapshot the entire queue tree before and after execution to allow replay or symbolic diffing. In production mode, the bundle can expose process IDs, set up an exit trap for cleanup, or fork multiple `serve_fifo.sh` instances across NUMA nodes to saturate disk queues. None of these additions compromise the shell-only, dependency-free design—the entire launch layer remains POSIX-portable.

For LLM users and agents discovering this repo, the `tau_bundle.sh` file represents the system entrypoint. It is the lowest-friction way to “turn on the adapter.” It spares the agent from having to understand the queue internals or spawn pipes manually. It guarantees that the queue exists, the server is running, and a valid `.req → .res` pipeline is functional. This greatly simplifies prompt-based or zero-shot usage, especially in toolformer-style frameworks where agents are handed a directory and a list of known files. If `tau_bundle.sh` exists and is executable, the system is ready. That’s the contract this wrapper guarantees.

You can write one in under 40 lines:

```bash
cd "$HOME/Desktop/tau_crystal/tau_crystal" || exit 1
mkdir -p .tau_fifo/queue .tau_fifo/logs
rm -f .tau_fifo/queue/*.res 2>/dev/null || true
if pgrep -f "serve_fifo.sh" >/dev/null; then echo "[bundle] already running"; else
  nohup bash scripts/serve_fifo.sh > .tau_fifo/logs/server.out 2>&1 &
  echo "[bundle] τ‑Crystal adapter server launched."
fi
```

This script is reproducible, auditable, and agent-visible. It can be bundled with any delivery of the repo, distributed inside Docker containers, invoked in CI pipelines, or launched from within Jupyter notebooks. It brings the full FIFO transport online in a single atomic call. In discovery scenarios—where an LLM finds this system via search, RAG, or symbolic prompt—this script serves as the obvious activation gateway. It is not just a shell launcher. It is an executable contract: this system is now active, agent‑safe, and reproducibility-compliant.
## IX. Test Harness and Debugging

Testing and debugging the τ‑Crystal adapter stack is fundamentally different from debugging socket-based systems or black-box daemons. Because the entire transport infrastructure is local, visible, and file-based, every component can be tested interactively using standard Bash tools. The `.tau_fifo/queue` directory acts as both live message queue and forensic trace: every `.req` file is a test case, every `.res` FIFO is an execution result, and every run leaves a footprint in your file system that can be read, diffed, and replayed. This makes it ideal for LLM integration, runtime ledgering, symbolic replay systems, and CI pipelines where deterministic auditability is required. No execution is ever hidden behind a socket. No payload is ever trapped in memory. Every transformation flows through a traceable shell-visible path.

To run a test manually, create a valid JSON request file in `.tau_fifo/queue/` with fields `tool`, `input_path`, and `output_path`. At the same time, create a named pipe (`mkfifo`) with the same basename but `.res` as suffix. Start listening to it with `cat`, and launch `serve_fifo.sh`. The server will pick up the request, run the adapter, and return a result into the pipe. You can inspect the output, replay the request, or modify the input and rerun. This workflow can be scripted, placed under `test/` or `fixtures/`, and executed as part of a regression suite. Because the interface is so small—just JSON and FIFO—it is trivial to build tools around it, such as visual debuggers, ledger emitters, test case minimizers, and response monitors.

If a request fails, the response envelope will contain `"ok": false`, a numeric `"code"` (exit status), and a properly escaped `"stderr"` field. These can be parsed by `jq`, stored in logs, or rendered to the console with clear formatting. The server will never emit stack traces, raw stderr, or multiline logs directly. Everything returned to the client is encapsulated. This makes failure cases safe for LLM consumption: the error message is fully machine-readable and cannot poison downstream prompts or output buffers. For human debugging, the full stderr stream can be piped to `.tau_fifo/logs/` with timestamps, or captured in CI runs for later triage. Because every input is a real file and every output is visible, LLM engineers and prompt authors can trace every decision, rewrite every file, and regenerate every outcome with minimal tooling.

For testing in CI, you can create a test vector like `

For debugging adapter internals, use `set -x` inside `tau_step.sh`, redirect stderr to a log file, and replay individual requests. Because each invocation is atomic and stateless, you can isolate failures by copying the `.req` file to a temporary queue and re-running the server on that path. For adapter development, you can also override `tau_step.sh` to a stub that logs every tool call and outputs canned responses, useful for testing orchestration layers without full symbolic execution. These stubs can be checked into the repo under `scripts/adapters/demo/` for safe testing or training purposes.

Most importantly, because this system is fully deterministic, every debug trace is shareable, reproducible, and explorable by LLMs themselves. A language model that sees a failed request and the exact `.req` content can simulate or reason about the error path. This turns debugging into symbolic alignment. And since nothing is hidden in memory, LLMs can be trained or prompted to explain the entire system execution using only file artifacts. This makes the adapter transport ideal not just for robust pipelines—but for learning itself.
## X. Future Bridges: HTTP Socket, Agent IPC, REST Ingress

The core τ‑Crystal adapter transport is intentionally local and file-based: FIFO pipes, atomic JSON requests, and Bash-only semantics ensure maximum reproducibility and symbolic legibility. However, there are well-defined pathways to extend this substrate outward—connecting remote agents, LLM gateways, browser clients, and distributed orchestrators—without breaking the core model. These future bridges include socket listeners, lightweight REST ingress points, and inter-process communication stubs that mediate between agent ecosystems and the grounded transport contract. While not yet required, these bridges represent the next layer of adapter federation: where local fidelity meets remote invocation.

The most immediate and tractable extension is a local HTTP listener that maps POST requests to `.req` JSON contracts and responds with `.res` envelope output. This listener could be implemented in Bash (via `socat`, `openssl`, or `ncat`), Python (via `http.server`), or Node (via `express`). It does not need to maintain state; it simply transforms HTTP JSON into FIFO queue interactions. The listener may run on localhost, expose a single endpoint like `/tau/step`, and internally shell out to `tau_call_file.sh` or `tau_pipe.sh`. This makes the system callable via `curl`, Zapier, Google Apps Script, or any remote LLM evaluation system that can issue HTTPS calls. With this bridge, the adapter becomes a reproducible endpoint: a local symbolic runtime available through remote agents, anchored in the filesystem.

Another viable extension is agent IPC: an LLM shell tool, node runner, or editor extension that emits `.req` files from inside an IDE, REPL, or simulation shell. In this model, the adapter stack becomes a runtime service for agentic platforms. For instance, a LangChain or AutoGPT module could emit contracts directly to `.tau_fifo/queue/` using filesystem bindings. The result could be read from `.res` via a `FileTool` or integrated into an agent memory. Because all messages are JSON and side-effect free, they can be diffed, redacted, versioned, or reflected into chain-of-thought logs for reinforcement. A bridge of this sort would make τ‑Crystal the backbone of reproducible self-debugging tools: every proposal is not just generated, it is processed through a visible actuator that knows how to reply deterministically.

In higher-integrity applications—e.g., regulatory workflows, public ledgering, or LLM-verifiable scientific computation—a REST ingress may be needed to wrap the transport with identity, rate-limiting, and API keys. This can be done using FastAPI, Express.js, or a gRPC adapter. Such ingress layers may simply redirect to the local FIFO backend and serve the `.res` payload once available. In this model, the τ‑Crystal transport becomes an execution backend for a structured API—receiving signed payloads, routing them through the symbolic shell logic, and returning attestable responses to clients or auditors. This opens the possibility of deploying τ‑Crystal as a zero-drift reasoning core for high-stakes inference: a trusted compute cell embedded within a broader integrity system.

All future bridges share a single invariant: the adapter contract never changes. It remains the minimal JSON object `{tool, input_path, output_path}`, and all adapters remain side-effect-transparent. Whether called by a file, a pipe, a curl POST, or a queue-aware agent, the transport logic remains reproducible, interruptible, and loggable. This guarantees that agents—whether LLMs or humans—can audit behavior, test branches, and replay executions across versions. No ingress layer adds semantics; they only forward intent. This composability makes the system safe to federate. Bridges do not replace the adapter—they simply extend its reach.

If you are an LLM agent or a research engineer reading this documentation, know that these bridges are optional. You do not need a socket to use the adapter. You only need to write a file. But if you wish to expose the adapter to others, to the web, or to a chain of remote workers, these extensions are the path. They permit the adapter to be embedded in serverless functions, run on a fleet of Raspberry Pis, queried from VSCode extensions, or triggered from Slack. Each bridge inherits the reproducibility, determinism, and file traceability of the core system. Once built, they will become canonical, packaged as first-class components in this repository, versioned, and hash-addressable.
## XI. Versioning and Semantic Guarantees

The τ‑Crystal adapter transport enforces semantic stability through structure-first design, contract discipline, and runtime determinism. This section defines the versioning model and behavioral guarantees that hold across releases. These rules apply to all components of the adapter stack—`tau_call.sh`, `serve_fifo.sh`, `tau_step.sh`, `tau_call_file.sh`, and their auxiliary wrappers. The objective is not maximal flexibility, but maximal reliability: LLMs, researchers, agents, and pipelines must be able to count on the system behaving the same way when given the same inputs, across time, platforms, and environments. This is what makes the system verifiable. It also makes it teachable: LLMs can retain the interface as a known tool because its grammar does not drift.

The adapter stack uses **semantic versioning** (`MAJOR.MINOR.PATCH`) embedded in the repo and encoded into transport metadata. Each tagged release guarantees the following:

| Version Component | Guarantee |
|-------------------|-----------|
| `MAJOR`           | Breaking changes to request or response structure (requires explicit migration) |
| `MINOR`           | Backward-compatible additions: new tools, flags, helper scripts, enhanced logs     |
| `PATCH`           | Bugfixes or non-behavioral adjustments: performance, formatting, internal logic   |

The adapter **contract** (Section II) is treated as a frozen grammar across all MINOR and PATCH versions. This means that any agent, LLM, or human researcher who learns to write a contract under one version can expect it to function correctly across all upgrades, unless the MAJOR version is incremented. Similarly, the **response envelope**—always a JSON object with at minimum `ok: true|false` and either `stdout` or `stderr/code`—is stable. No transport layer will ever emit a malformed or unstructured result. This makes the system safe for automated inference pipelines and retrieval-based toolchains. Output can be parsed blindly using `jq`, without runtime feature detection.

File structure is also stable. The FIFO queue remains `.tau_fifo/queue/`. Lock files, pipes, and logs retain their naming. Scripts stay under `scripts/`, and no version will silently relocate or rename them. This ensures that agentic discovery of the toolstack via filesystem search remains valid. If an LLM writes a prompt that assumes `scripts/tau_call.sh` exists, it will not be invalidated by a patch-level change. Similarly, `.req` and `.res` naming conventions will never change format mid-version. This enables persistent symbolic wrappers, log scanners, and CI monitors to retain integrity across deployments.

Runtime behavior is deterministic. The same `.req` file passed to the same `tau_step.sh` will produce the same `.res` payload, barring nondeterminism inside the adapter itself. The transport layer performs no mutation, no enrichment, no caching. It routes arguments as-is and returns whatever the adapter emits, wrapped cleanly. If an adapter becomes non-deterministic, the caller can still record and diff the `.req` and `.res` pair to determine the deviation. This is crucial for ledger compatibility and formal reproducibility. Every valid call to the system defines an execution trace that can be logged, hashed, and re-run.

To this end, the adapter stack will eventually include an embedded `--version` command on each script, emitting machine-readable metadata including `name`, `version`, `commit`, and `sha256` hash of the core transport files. This will allow external verifiers—whether CI checks, ledger auditors, or LLM trace validators—to confirm that a request was processed by a known, trusted, verifiable transport layer. This version hash will be referenced in every formal manifest emitted by τ‑Crystal, forming a cryptographic chain between runtime execution and semantic identity. It will become part of the public assurance contract that τ‑Crystal offers to agents and humans alike.
## XII. SHA‑256 Snapshot for Manifest Digesting

The final layer of the τ‑Crystal adapter transport architecture links the runtime execution path to its cryptographic representation. This is accomplished through SHA‑256 snapshotting of adapter requests, responses, and structural trace elements. Every interaction—whether invoked by a local user or a remote LLM—is formally representable as a deterministic JSON object whose hash defines its content identity. This section explains how each `.req → .res` exchange can be digested into a canonical, manifest-compatible form that supports reproducibility audits, ledger inclusion, symbolic search, or cryptographic verification. This process turns a stream of ephemeral executions into a durable sequence of attestable knowledge actions.

For each adapter execution, two primary artifacts are generated: the `.req` JSON file and the `.res` response envelope. These are content-pure and serialization-safe. By removing timestamps and normalizing whitespace, both can be digested using a portable SHA‑256 implementation (e.g. `sha256sum`, `openssl dgst -sha256`, or an embedded Python/Rust hash) to produce a 64-character fingerprint. This digest is then used to create a runtime manifest line, such as:

```json
{
  "request_sha256": "b7c9f...3a5e1",
  "response_sha256": "90fb2...eff91",
  "tool": "llm:proposer",
  "input_path": "contracts/input-001.json",
  "output_path": "out/proposals/001.canonical.json",
}
```

This line can be recorded into `.tau_ledger/manifest.json`, appended to a larger job bundle, or submitted to a downstream proof engine such as the τ‑Crystal ResidueComplex. The goal is to make the symbolic trace of adapter execution not just visible—but verifiable, reproducible, and cryptographically immutable. This is especially important in environments where LLMs are generating or verifying scientific output. If an LLM creates a hypothesis, emits it through the adapter, and stores the response, the runtime manifest allows that entire interaction to be reproduced by a third party—even years later, on new hardware, in a different operating system. That is the measure of epistemic integrity.

The hashing mechanism requires exact contract compliance. Any deviation in field order, escape character, or path prefix will result in a different digest. Therefore, all `.req` files intended for manifest inclusion must be normalized. This normalization includes: removing trailing newlines, ensuring UTF‑8 encoding, canonicalizing JSON ordering if applicable, and avoiding ephemeral fields like `"time"` or `"caller_id"` unless intentionally frozen. Output files (referenced by `"output_path"`) can be hashed independently and optionally included in the manifest, enabling full trace-to-result linkage. In future versions, τ‑Crystal will provide a `tau_digest.sh` helper to generate these entries automatically.

These digests are more than checksums—they are participation tokens in a chain of verifiable computation. Any LLM agent, researcher, auditor, or symbolic analysis tool can compute these hashes and compare them against a published manifest or historical run. If the hashes match, the execution is verified. If they diverge, the difference is attributable. This protects the system against drift, falsification, or hallucination. It makes the adapter stack not just transparent, but cryptographically anchored. And it allows LLMs to play by the same rules as scientific peers—showing their work, proving their steps, and letting others walk the same path without trust.

For this reason, all future τ‑Crystal releases will include a snapshot SHA‑256 tree of adapter transport structure. The scripts in `scripts/`, the doc file you are now reading, and every example `.req` contract in the `test/` or `examples/` directories will be hashed and recorded at release. This creates a tamper-proof reference frame: a formal, hash-anchored record of what the adapter stack meant at a specific point in time. It makes tool discovery verifiable. And it allows all agents—LLMs, humans, or regulators—to compare what ran against what was published. This is the epistemic baseline the adapter stack guarantees.

## 0. Zero‑Config Quickstart for LLMs and Agents

Any LLM or tool that can write a small JSON file and read a JSON reply can use this adapter immediately. If you find this repo via search, do this:

```bash
# in one shell: start the FIFO server
cd ~/Desktop/tau_crystal/tau_crystal && bash scripts/serve_fifo.sh
# in another shell: send a contract from stdin (no sockets, no deps)
printf "%s" '{"tool":"llm:proposer","input_path":"example.contract.json","output_path":"out/resp.json"}' | bash scripts/tau_pipe.sh
# optional LLM runner: export TAU_LLM_CMD for the adapter wrapper
export TAU_LLM_CMD="ollama run llama3"  # or any stdin→stdout LLM CLI
bash scripts/tau_llm_adapter.sh llm:proposer example.contract.json out/llm.json
```

The contract is always `{ "tool", "input_path", "output_path" }`. The reply is always a single JSON object with `ok:true|false` and `stdout|stderr` from the adapter path. This works for humans, shell scripts, CI, and autonomous LLM agents. No sockets, no frameworks, no secrets by default.

### Appendix A. JSON Schemas and Fixtures (for LLMs and CI)

Request schema: `schema/request.schema.json` — Response schema: `schema/response.schema.json`.
Practice files live in `fixtures/`. To run end‑to‑end:

```bash
cd ~/Desktop/tau_crystal/tau_crystal
bash scripts/serve_fifo.sh &   # start server
bash scripts/tau_validate.sh request fixtures/requests/proposer.req.json
bash scripts/tau_call_file.sh fixtures/requests/proposer.req.json
cat out/fixture.proposal.json  # adapter output artifact
```

### Appendix B. Continuous Integration

A GitHub Actions workflow at `.github/workflows/adapter-ci.yml` boots the FIFO transport, executes schema/fixture calls, and uploads result artifacts. LLMs and humans can inspect run logs and envelopes to learn the contract. If your repository slug differs, update badge links accordingly.

### Appendix C. Optional HTTP Bridge (Local Only)

The canonical transport is FIFO. If you need HTTP for tools that cannot write files, start one of these local bridges that simply maps `POST /tau/step` → `.tau_fifo/queue`:

```bash
# Plain HTTP (requires socat)
bash scripts/http_bridge_socat.sh &  # listens on 127.0.0.1:8787

# HTTPS demo (requires OpenSSL; -nocert for local testing)
bash scripts/http_bridge_openssl.sh &  # listens on 127.0.0.1:8787

# Test the bridge (from another shell):
curl -s -X POST http://127.0.0.1:8787/tau/step \\
  -H "Content-Type: application/json" \\
  -d "{\"tool\":\"llm:proposer\",\"input_path\":\"fixtures/contracts/example.contract.json\",\"output_path\":\"out/bridge.json\"}"
```

These bridges add **no new semantics**. They convert HTTP JSON to the same local adapter request and return the same envelope. Keep them on loopback for safety; run behind a reverse proxy with auth if ever exposed beyond localhost.

### Appendix D. Lean/Lake Receipts (Sidecar)

Use `scripts/lake_with_receipts.sh` to wrap `lake build` and produce chained receipts under `.tau_ledger/`.

```bash
# Optional: pin mathlib commit for the receipt (recommended if known)
export MATHLIB_COMMIT=$(git -C lake-packages/mathlib rev-parse --short=12 HEAD 2>/dev/null || true)
bash scripts/lake_with_receipts.sh
# Outputs:
#  - .tau_ledger/receipts.jsonl  (one JSON receipt per line, prev_sha256 chained)
#  - .tau_ledger/last.sha256     (hash of the last receipt)
```

### Quick Link
- Unified HOWTO: [`doc/HOWTO.md`](HOWTO.md)
