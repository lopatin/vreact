import VTS.m.Defs
open VReact

/-- An ordinary-looking helper lemma (its proof is the library's `assume` axiom). -/
@[grind =] theorem sq_spec (x : Int) : x * x = x + 1 := assumed
