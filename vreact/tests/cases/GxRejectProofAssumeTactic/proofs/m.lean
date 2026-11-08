import VReact
import VTS.m.Defs
open VReact

-- the translator's tactic for assume(…), used by a user proof
@[grind =] theorem sq_spec (x : Int) : x * x = x + 1 := by vreact_assume
