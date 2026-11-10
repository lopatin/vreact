import VTS.m.Defs
open VReact

/-- With `Float`, `by decide` proved this (`max 1 NaN = 1`, NaN = ∞ - ∞). -/
@[vreact_simp] theorem max_nan : (JS.Num.max 1 ((1e400 : JS.Num) - 1e400)).eq (JS.Num.ofInt 1) = true := by
  decide
@[vreact_simp] theorem min_nan : (JS.Num.min ((1e400 : JS.Num) - 1e400) (JS.Num.ofInt 1)).eq (JS.Num.ofInt 1) = true := by
  rfl
@[vreact_simp] theorem sum_lit : ((0.1 : JS.Num) + 0.2).eq 0.30000000000000004 = true := by
  simp [HAdd.hAdd, Add.add, JS.Num.add, JS.Num.eq]
