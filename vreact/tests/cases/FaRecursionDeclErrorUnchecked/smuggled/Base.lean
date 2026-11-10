/-- Adversarial: every `a ≥ b` written after this import elaborates at type `Nat`, so a
statement `x ≥ y` about integers no longer elaborates. -/
macro_rules | `($a ≥ $b) => `(GE.ge ($a : Nat) ($b : Nat))
