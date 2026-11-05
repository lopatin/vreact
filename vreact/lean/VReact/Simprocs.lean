import Lean
import VReact.JS
import VReact.Attr
/-!
# Simprocs: evaluate source string literals

`JS.Str.ofString "abc"` (a string literal of the program) is rewritten to its
UTF-16 code units `⟨[97, 98, 99]⟩`, so lengths, emptiness and equalities of
literal strings are decided by `simp`.  The rewrite is definitional (`dsimproc`):
the kernel re-checks it by unfolding `ofString`.
-/
namespace VReact
open Lean Meta Simp

dsimproc [vreact_simp] reduceOfString (JS.Str.ofString _) := fun e => do
  let_expr JS.Str.ofString arg ← e | return .continue
  let .lit (.strVal s) := arg | return .continue
  let units := s.toList.flatMap JS.Str.encodeChar
  let u16 := mkConst ``UInt16
  let elems ← units.mapM fun u => mkNumeral u16 u.toNat
  let lst ← mkListLit u16 elems
  return .done (mkApp (mkConst ``JS.Str.mk) lst)

/-- Record fields through a conditional: `(if c then a else b).f` ↦ `if c then a.f else b.f`
(also for `dite`).  State updates are written `xs.map(x => cond ? {...x, f: v} : x)`; with
this rewrite every field that the update does not touch collapses to `x.f` (`ite_self`),
so facts about untouched fields (distinct ids, bounds on other fields) carry over
syntactically instead of by case analysis inside the lambda.  Only structure
projections are rewritten (the proof is `apply_ite`/`apply_dite`). -/
simproc [vreact_simp] pushProjIte (_) := fun e => do
  let .const fn _ := e.getAppFn | return .continue
  let some info ← getProjectionFnInfo? fn | return .continue
  if info.fromClass then return .continue
  unless e.getAppNumArgs == info.numParams + 1 do return .continue
  let s := e.appArg!
  let f := e.appFn!
  unless s.isAppOfArity ``ite 5 || s.isAppOfArity ``dite 5 do return .continue
  let #[_, c, inst, a, b] := s.getAppArgs | return .continue
  let ty ← inferType e
  let thm := if s.isAppOfArity ``ite 5 then ``apply_ite else ``apply_dite
  let pf ← mkAppOptM thm #[none, ty, f, c, inst, a, b]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

end VReact
