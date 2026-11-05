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
  let .const cond [u] := s.getAppFn | return .continue
  unless (cond == ``ite || cond == ``dite) && s.getAppNumArgs == 5 do return .continue
  let #[α, c, inst, a, b] := s.getAppArgs | return .continue
  -- The terms are built directly (no `mkAppM`): simp has already rewritten `c` but not
  -- the instance `inst`, which is only definitionally of type `Decidable c`.
  try
    let f := e.appFn!
    let β ← inferType e
    let v ← getLevel β
    if cond == ``ite then
      let rhs := mkApp5 (mkConst ``ite [v]) β c inst (mkApp f a) (mkApp f b)
      let pf := mkApp7 (mkConst ``apply_ite [u, v]) α β f c inst a b
      return .visit { expr := rhs, proof? := some pf }
    else
      let br (x : Expr) (ty : Expr) : Expr :=
        .lam `h ty (mkApp f (x.beta #[.bvar 0])) .default
      let rhs := mkApp5 (mkConst ``dite [v]) β c inst (br a c) (br b (mkNot c))
      let pf := mkApp7 (mkConst ``apply_dite [u, v]) α β f c inst a b
      return .visit { expr := rhs, proof? := some pf }
  catch _ => return .continue

end VReact
