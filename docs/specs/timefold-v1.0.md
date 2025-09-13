# τ‑Crystal timefold v1.0

A timefold is a rewindable snapshot comprising a deterministic file list, a gzipped tar archive, and a stamped manifest section. The meta file records id, label, UTC, archive name, sha256, bytes, and file count. Verification recomputes sha256 over the archive and compares to the manifest.
