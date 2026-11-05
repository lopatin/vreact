/-- Adversarial: `bump` becomes a token, so the generated declarations named `bump` no
longer parse (Lean skips them up to the next command). -/
syntax "bump" : term
