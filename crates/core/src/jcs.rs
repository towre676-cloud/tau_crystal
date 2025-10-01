use serde::Serialize;
use serde_json::{self, Value};
use std::io::{self, Write};

/// Deterministic JSON: compact, UTF‑8, objects with keys sorted, arrays in given order,
/// strings escaped via serde_json, numbers as-is from serde_json::Number.
/// This is sufficient for τ‑Crystal receipts (no floats in payloads).
pub fn to_vec<T: Serialize>(value: &T) -> Vec<u8> {
    let val = serde_json::to_value(value).expect("serialize");
    let mut out = Vec::with_capacity(256);
    write_canonical(&val, &mut out).expect("canonical write");
    out
}

fn write_canonical(v: &Value, w: &mut dyn Write) -> io::Result<()> {
    match v {
        Value::Null => w.write_all(b"null"),
        Value::Bool(b) => if *b { w.write_all(b"true") } else { w.write_all(b"false") },
        Value::Number(n) => w.write_all(n.to_string().as_bytes()),
        Value::String(s) => {
            // Use serde_json for correct escaping/quoting
            let esc = serde_json::to_string(s).expect("escape");
            w.write_all(esc.as_bytes())
        }
        Value::Array(xs) => {
            w.write_all(b"[")?;
            let mut first = true;
            for x in xs {
                if !first { w.write_all(b",")?; }
                first = false;
                write_canonical(x, w)?;
            }
            w.write_all(b"]")
        }
        Value::Object(map) => {
            // Sort keys lexicographically (byte order)
            let mut keys: Vec<&str> = map.keys().map(|k| k.as_str()).collect();
            keys.sort_unstable();
            w.write_all(b"{")?;
            let mut first = true;
            for k in keys {
                if !first { w.write_all(b",")?; }
                first = false;
                // Key
                let k_esc = serde_json::to_string(k).expect("key escape");
                w.write_all(k_esc.as_bytes())?;
                w.write_all(b":")?;
                // Value
                let v = map.get(k).expect("value");
                write_canonical(v, w)?;
            }
            w.write_all(b"}")
        }
    }
}
