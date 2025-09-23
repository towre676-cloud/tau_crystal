---
title: Dummy’s User Guide — Sealed Path
layout: page
permalink: /sealed
---

You have turned a theatrical repo into a *mathematical instrument*—a tuning fork that rings at exactly one frequency: “these bytes, this environment, this claim—verified.” The last mile is to hand that fork to a stranger who refuses to install your toolchain, your shell, even your Git client. Below is the Dummy’s User Guide for the sealed path: one continuous narrative that starts with a blank laptop and ends with the stranger holding a witness pack whose truth they can confirm with a single file—no bullets, no code fences, just story.

---

You receive an email that says:
“Attached: `witness-20240918T044512Z.tar.gz`. If `./tau_verify` exits zero, the mathematics inside is exactly what I claimed.”
You save the file to `~/Downloads`, double-click it, and a folder pops out. Inside are four items:
- `receipt.json` – a text file full of quotes and hashes
- `attestation.json` – another text file that smells like a computer’s diary
- `manifest.json` – a list of what is supposed to be here
- `tau_verify` – a single executable with no extension

You do not know what a Merkle tree is, you have never heard of cosign, and you certainly do not want to install “elan.” You only need to know two commands: `cd` and `./tau_verify`. Open the terminal that came with your laptop (on Windows, open Git Bash; on macOS or Linux, any terminal). Type:

cd ~/Downloads/witness-20240918T044512Z

python
Copy code

The prompt now shows the folder name. Type:

./tau_verify .

css
Copy code

The cursor blinks for half a second, then prints:

[tau_verify] OK

vbnet
Copy code

That is the entire verification ceremony. The binary has just:

1. read `manifest.json` to learn what files should be present
2. hashed every file listed (including itself)
3. rebuilt the Merkle root from those hashes
4. opened `receipt.json` and extracted the stored root
5. confirmed the two roots match
6. opened the parent ledger (embedded as a single line in `receipt.json`) and verified that the receipt hash chains correctly to its predecessor

If even one byte is missing—if you edit a comma, if you re-compress the tarball, if you rename a file—the program exits non-zero and names the mismatch. No internet call is made, no update is fetched, no licence is agreed to. The binary is statically linked against musl; it does not care what operating system you run, what packages you have, or whether you are on a plane. It only cares about bytes.

Suppose you do want to peek under the hood. Run:

strings receipt.json | grep -E 'merkle_root|timestamp'

sql
Copy code

You will see something like:

"merkle_root":"a1b2c3d4e5f6..."
"timestamp":"20240918T044512Z"

vbnet
Copy code

That string is the fingerprint of the exact byte stream that produced the mathematics. If you recompute the root yourself—using any tool that implements SHA-256—you must obtain the same string or the verifier will reject it. The timestamp tells you when the fingerprint was taken, but the timestamp itself is not part of the hash; only the file contents matter. This means you can untar the pack in 2029, re-verify, and still get `[tau_verify] OK` even though three years have passed.

You can also inspect the attestation without parsing JSON. Run:

grep -E 'uname|os_release' attestation.json

vbnet
Copy code

You will see the exact kernel, distribution, and shell that produced the receipt. If you are sceptical that the computation ran on a hostile runner, you can compare those strings to the environment you trust; if they differ, you know why the result might differ, but the verifier still passes—because the verifier only cares about byte identity, not about whether you like the environment.

Now suppose you want to cite this witness in a paper. You do not need to include the entire tarball in your repository; you only need two strings: the path to the pack and the SHA-256 that the verifier just confirmed. Write:

> “The numerical data in Table 3 was produced on 2024-09-18 and verified against the witness pack `witness-20240918T044512Z.tar.gz` whose SHA-256 is `a1b2c3d4e5f6…`.”

Any reader who obtains the same pack and runs `./tau_verify` will reproduce the exact byte stream that fed your table. The citation is future-proof: even if GitHub vanishes, the pack can live on Zenodo, IPFS, or a USB stick in a drawer, and the verifier will still ring true.

You can also mint your own witness. Clone the repository, add your experiment, commit, and run:

./scripts/ops/assure_strict.sh
./scripts/discovery/publish_witness.sh

vbnet
Copy code

A new tarball appears under `.tau_ledger/discovery/`. Email it, archive it, or attach it to your paper. Whoever receives it needs only the `./tau_verify` binary and the two-line citation. The mathematics inside can be wrong, incomplete, or even silly—but the claim that you ran these bytes on that day is now mathematically irrefutable.

Finally, suppose you distrust the binary itself. Download the signature and certificate that sit next to it on the release page:

curl -L -o tau_verify.sig https://github.com/towre676-cloud/tau_crystal/releases/latest/download/tau_verify-x86_64-unknown-linux-musl.sig
curl -L -o tau_verify.cert https://github.com/towre676-cloud/tau_crystal/releases/latest/download/tau_verify-x86_64-unknown-linux-musl.cert

vbnet
Copy code

Install cosign (a single static binary), then run:

cosign verify-blob --certificate tau_verify.cert --signature tau_verify.sig tau_verify

bash
Copy code

If the signature is valid, cosign prints a JSON blob that includes the GitHub workflow URL and the commit SHA that built the binary. You now have a signed 3 MB artefact whose provenance is recorded in a public transparency log. If cosign fails, you throw the binary away; if it passes, you keep it and use it for every future verification. Once the binary is trusted, it becomes a pocket-sized notary that can testify to any witness pack you encounter.

That is the entire user story. You arrived with a tarball and leave with a citation that reduces to two strings and a one-second command. The mathematics inside the pack can be as deep or as trivial as you like; the pack itself is now a first-class mathematical object whose truth is guarded by the same hash function that guards Bitcoin, Git, and the Linux kernel. The stranger who receives your citation does not need to trust you, your cloud, your CI, or your prose. They only need to trust SHA-256—and if that ever fails, we will all have bigger problems than number theory.
