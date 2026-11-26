//! モデルのdigest。
//!
//! digestは、IRからソース位置（`source`）を除き、キーを整列して直列化したJSONのSHA-256である。
//! ソース位置だけが違うIRは同じモデルとして扱う。

use serde_json::Value;
use sha2::{Digest, Sha256};

fn write(v: &Value, out: &mut String) {
    match v {
        Value::Object(map) => {
            let mut keys: Vec<&String> = map.keys().filter(|k| k.as_str() != "source").collect();
            keys.sort();
            out.push('{');
            for (i, k) in keys.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&Value::String((*k).clone()).to_string());
                out.push(':');
                write(&map[*k], out);
            }
            out.push('}');
        }
        Value::Array(items) => {
            out.push('[');
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write(item, out);
            }
            out.push(']');
        }
        other => out.push_str(&other.to_string()),
    }
}

pub fn digest(v: &Value) -> String {
    let mut text = String::new();
    write(v, &mut text);
    let hash = Sha256::digest(text.as_bytes());
    let mut out = String::from("sha256:");
    for b in hash {
        out.push_str(&format!("{b:02x}"));
    }
    out
}
