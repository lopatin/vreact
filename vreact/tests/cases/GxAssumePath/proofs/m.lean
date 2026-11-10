import VReact
import VTS.m.Defs
open VReact

-- the assumed facts as Lean keeps them: under the path (`flag = true`) and the precondition
theorem g_fact : ∀ flag : Bool, flag = true → flag = true := VTS.m.g._proof_1
theorem h_fact : ∀ x : Int, x > 0 → x * x > 0 := VTS.m.h._proof_1

-- a lemma about g that relies on g's definition (and so on its assume(…), the program's)
@[vreact_simp] theorem g_nonneg (flag : Bool) : 0 ≤ VTS.m.g flag := by
  unfold VTS.m.g; split <;> decide
