import VReact
import VTS.top.Defs
open VReact

-- the axiom by its full name (the finding's case: no assume(…) in `one`)
@[vreact_simp] theorem one_eq_two : (1 : Int) = 2 := VReact.assumed

-- through a renaming `open`
open VReact renaming assumed → fact in
@[vreact_simp] theorem five_eq_six : (5 : Int) = 6 := fact

-- through an auxiliary definition (the definition is named)
def anything {p : Prop} : p := VReact.assumed
@[vreact_simp] theorem three_eq_four : (3 : Int) = 4 := anything

-- through a tactic
@[vreact_simp] theorem seven_eq_eight : (7 : Int) = 8 := by apply VReact.assumed

-- unfolds a function whose body has an assume(…): its proof refers to the generated
-- declarations only (the assumed fact is the program's)
@[vreact_simp] theorem get_first : VTS.top.get' [10, 20] 0 = 10 := by
  unfold VTS.top.get'; rfl
