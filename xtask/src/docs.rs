//! `xtask docs` -- deterministic `CONFORMANCE.md` from `model/claims.json`.
//! SPEC section 17.3. Replaces `Tools/gen_conformance.py`.
//!
//! Regeneration is byte-identical, which is what lets `reproducible.yml` assert
//! the committed file is clean afterwards. The inventory line is computed LIVE
//! from the tree: prose documents cite this table rather than repeating counts,
//! because the counts copied into prose kept going stale.

use std::path::Path;

use crate::json::{self, Value};
use crate::lean;
use crate::repo;
use crate::spec::{Outcome, Result, SpecError};

const CLAUSE: &str = "17.3";
const OUTPUT: &str = "CONFORMANCE.md";

pub fn run() -> Result<Outcome> {
    let registry = read_registry()?;
    let claims = registry
        .get("claims")
        .and_then(Value::as_array)
        .ok_or_else(|| SpecError::new(CLAUSE, "model/claims.json has no `claims` array"))?;

    let text = render(&registry, claims)?;
    std::fs::write(Path::new(OUTPUT), &text)
        .map_err(|e| SpecError::io(CLAUSE, "cannot write", Path::new(OUTPUT), e))?;

    let outstanding = claims.iter().filter(|c| status(c) == "outstanding").count();
    println!("{OUTPUT}: {} claims, {outstanding} outstanding", claims.len());
    Ok(Outcome::Pass)
}

fn read_registry() -> Result<Value> {
    let path = Path::new("model/claims.json");
    let text = std::fs::read(path)
        .map(|b| String::from_utf8_lossy(&b).into_owned())
        .map_err(|e| SpecError::io(CLAUSE, "cannot read the claim registry", path, e))?;
    json::parse(CLAUSE, &text)
}

fn render(registry: &Value, claims: &[Value]) -> Result<String> {
    let (modules, lines, theorems) = inventory()?;
    let mut l: Vec<String> = Vec::new();

    l.push("# Conformance\n".into());
    l.push(format!(
        "**Inventory:** {modules} Lean modules, {} lines, {} proved theorems.",
        commas(lines),
        commas(theorems)
    ));
    l.push("Generated live; prose documents cite this table rather than repeating counts.\n".into());
    l.push("Generated from `model/claims.json` by `just docs`. Do not edit by hand.\n".into());
    l.push("Claim levels are load-bearing (SPEC 17.1). Only `formalProof` supports the".into());
    l.push("words \"proved\", \"theorem\", or \"globally optimal\".\n".into());
    l.push("## Claims\n".into());
    l.push("| ID | Level | Status | Statement | Lean declaration |".into());
    l.push("| --- | --- | --- | --- | --- |".into());
    for c in claims {
        let decl = declaration(c);
        let statement = truncate(&statement(c).replace('|', "\\|"), 110, 107);
        l.push(format!(
            "| `{}` | {} | {} | {statement} | `{decl}` |",
            field(c, "id"),
            field(c, "level"),
            status(c)
        ));
    }

    l.push("\n## Axiom closure\n".into());
    l.push("Every `formalProof` claim's transitive axioms, from `#print axioms`:\n".into());
    for c in claims {
        if field(c, "level") == "formalProof" {
            let axioms: Vec<String> = c
                .get("axioms")
                .and_then(Value::as_array)
                .unwrap_or(&[])
                .iter()
                .filter_map(Value::as_str)
                .map(|a| format!("`{a}`"))
                .collect();
            let rendered = if axioms.is_empty() { "none".to_string() } else { axioms.join(", ") };
            l.push(format!("- `{}` — {rendered}", field(c, "id")));
        }
    }
    l.push("\nPermitted: `propext`, `Quot.sound`, `Classical.choice` (Lean core logical".into());
    l.push("axioms, SPEC 4). Any `sorryAx` or project-declared axiom fails the gate.\n".into());

    l.push("## Refuted framings\n".into());
    l.push("Recorded so they are not silently re-asserted:\n".into());
    for r in registry
        .get("refutedFramings")
        .and_then(Value::as_array)
        .unwrap_or(&[])
    {
        l.push(format!(
            "- **{}** ({}) — {}",
            field(r, "verdict"),
            field(r, "confidence"),
            field(r, "framing")
        ));
        l.push(format!("  - {}", field(r, "reason")));
    }

    l.push("\n## Outstanding obligations\n".into());
    let outstanding: Vec<&Value> = claims.iter().filter(|c| status(c) == "outstanding").collect();
    l.push(format!(
        "{} outstanding. Terminal answer for `GO-001`: `WorkloadIncomplete`",
        outstanding.len()
    ));
    l.push("(UOR-GNAF v1-draft.2 section 10.9). See `CERTIFICATION.md`.\n".into());
    for c in outstanding {
        let obligation = c
            .get("obligation")
            .and_then(Value::as_str)
            .unwrap_or("—");
        l.push(format!(
            "- `{}` ({obligation}) — {}",
            field(c, "id"),
            take_chars(&statement(c), 100)
        ));
    }

    Ok(l.join("\n") + "\n")
}

/// Live inventory: modules, lines and proved theorems under `WasmGemmGnaf/`.
fn inventory() -> Result<(usize, usize, usize)> {
    let modules = repo::lean_files("17.3", Path::new("WasmGemmGnaf"))?;
    let mut lines = 0usize;
    let mut theorems = 0usize;
    for module in &modules {
        let text = repo::read_lossy("17.3", module)?;
        for line in lean::splitlines(&text) {
            lines += 1;
            if line.trim_start().starts_with("theorem ") {
                theorems += 1;
            }
        }
    }
    Ok((modules.len(), lines, theorems))
}

fn field<'a>(value: &'a Value, key: &str) -> &'a str {
    value.get(key).and_then(Value::as_str).unwrap_or("")
}

fn status(claim: &Value) -> &str {
    field(claim, "status")
}

fn statement(claim: &Value) -> String {
    field(claim, "statement").to_string()
}

/// `leanDeclaration`, or an em dash when it is absent or empty.
fn declaration(claim: &Value) -> &str {
    match claim.get("leanDeclaration").and_then(Value::as_str) {
        Some(d) if !d.is_empty() => d,
        _ => "—",
    }
}

/// Keep at most `limit` characters, eliding to `keep` plus `...` when longer.
fn truncate(text: &str, limit: usize, keep: usize) -> String {
    if text.chars().count() <= limit {
        text.to_string()
    } else {
        format!("{}...", take_chars(text, keep))
    }
}

fn take_chars(text: &str, n: usize) -> String {
    text.chars().take(n).collect()
}

/// Thousands separators, as Python's `format(n, ",")` writes them.
fn commas(n: usize) -> String {
    let digits = n.to_string();
    let mut out = String::with_capacity(digits.len() + digits.len() / 3);
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thousands_separators_match_python() {
        assert_eq!(commas(0), "0");
        assert_eq!(commas(999), "999");
        assert_eq!(commas(1000), "1,000");
        assert_eq!(commas(31337), "31,337");
        assert_eq!(commas(1234567), "1,234,567");
    }

    #[test]
    fn statement_truncation_is_by_character() {
        let short = "a".repeat(110);
        assert_eq!(truncate(&short, 110, 107), short);
        let long = "a".repeat(111);
        let cut = truncate(&long, 110, 107);
        assert_eq!(cut.chars().count(), 110);
        assert!(cut.ends_with("..."));
        // Multi-byte characters must not be split mid-character.
        let wide = "é".repeat(200);
        assert_eq!(truncate(&wide, 110, 107).chars().count(), 110);
    }

    #[test]
    fn absent_declaration_becomes_an_em_dash() {
        let v = json::parse("17.3", r#"{"leanDeclaration": null}"#).expect("parses");
        assert_eq!(declaration(&v), "—");
        let v = json::parse("17.3", r#"{"leanDeclaration": "A.b"}"#).expect("parses");
        assert_eq!(declaration(&v), "A.b");
    }
}
