Each line is a JSON object:
- type: "lock" | "step" | "commit" | "error"
- ts:   RFC3339 timestamp
- data: type-dependent payload

LOCK line:
{"type":"lock","ts":"...","data":{"contract_sha256":"...","contract_path":"..."}}

STEP line:
{"type":"step","ts":"...","data":{"tool":"<name>","input_sha256":"...","output_sha256":"...","meta":{}}}

COMMIT line:
{"type":"commit","ts":"...","data":{"trace_sha256":"...","receipt_sha256":"...","receipt_path":"..."}}
