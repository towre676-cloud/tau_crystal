# τ‑Crystal sheaf‑reflect v1.0

Definition: given the normalized CHAIN (LF line endings, trailing spaces removed), compute a rolling hash R_i = sha256(R_{i-1} || ' ' || h_i) with R_0 = '0'; the preimage is the UTF‑8 lines: 'tau_sheaf_v1', 'lines:<N>', 'stamp:<UTC>', and 'r<i>:<R_i>' for i = 1..N. The sheaf_digest is sha256(preimage).

Stability: independent of OS newlines, shell locale, or whitespace at line end. Security: any insertion, deletion, or permutation in CHAIN perturbs the digest.
