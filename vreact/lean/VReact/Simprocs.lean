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

/-- `String(7)`, `` `${-12}` ``, `` `${true}` `` of a literal: the literal string of its decimal
rendering (`JS.str` of `Int`/`Nat`/`Bool`, by its definition), then `reduceOfString`.
Definitional (`dsimproc`): the kernel re-checks it by evaluating `toString`. -/
dsimproc [vreact_simp] reduceStrOfLit (JS.str _) := fun e => do
  let_expr JS.str ty inst x ← e | return .continue
  let some tn := ty.constName? | return .continue
  let s? : Option String ←
    if tn == ``Int && inst.isConstOf ``JS.instToJSInt then pure ((← getIntValue? x).map toString)
    else if tn == ``Nat && inst.isConstOf ``JS.instToJSNat then pure ((← getNatValue? x).map toString)
    else if tn == ``Bool && inst.isConstOf ``JS.instToJSBool then
      pure (if x.isConstOf ``true then some "true" else if x.isConstOf ``false then some "false" else none)
    else pure none
  let some s := s? | return .continue
  return .visit (mkApp (mkConst ``JS.Str.ofString) (mkStrLit s))

/-- Concatenation of two literal strings (code-unit list literals, as `reduceOfString` leaves
them) is a literal: `"a" + "b" === "ab"`, template literals with literal parts.  Together
with `Str.append_assoc` (`(s + "a") + "b"` ↦ `s + "ab"`).  Definitional (`dsimproc`). -/
dsimproc [vreact_simp] reduceStrAppend ((_ : JS.Str) ++ (_ : JS.Str)) := fun e => do
  let_expr HAppend.hAppend _ _ _ _ a b ← e | return .continue
  let_expr JS.Str.mk la ← a | return .continue
  let_expr JS.Str.mk lb ← b | return .continue
  let some (_, xs) := la.listLit? | return .continue
  let some (_, ys) := lb.listLit? | return .continue
  return .done (mkApp (mkConst ``JS.Str.mk) (← mkListLit (mkConst ``UInt16) (xs ++ ys)))

@[vreact_simp] theorem JS.Str.append_assoc (a b c : JS.Str) : a ++ b ++ c = a ++ (b ++ c) := by
  cases a; cases b; cases c
  exact congrArg JS.Str.mk (List.append_assoc _ _ _)

/-- Record fields through a conditional: `(if c then a else b).f` ↦ `if c then a.f else b.f`
(also for `dite`).  State updates are written `xs.map(x => cond ? {...x, f: v} : x)`; with
this rewrite every field that the update does not touch collapses to `x.f` (`ite_self`),
so facts about untouched fields (distinct ids, bounds on other fields) carry over
syntactically instead of by case analysis inside the lambda.  Only structure
projections are rewritten (the proof is `apply_ite`/`apply_dite`). -/
simproc [vreact_simp] pushProjIte (_) := fun e => do
  -- cheap syntactic checks first: this simproc is tried on every subterm
  let .app f s := e | return .continue
  let .const cond [u] := s.getAppFn | return .continue
  unless (cond == ``ite || cond == ``dite) && s.getAppNumArgs == 5 do return .continue
  let .const fn _ := e.getAppFn | return .continue
  let some info ← getProjectionFnInfo? fn | return .continue
  if info.fromClass then return .continue
  unless e.getAppNumArgs == info.numParams + 1 do return .continue
  let #[α, c, inst, a, b] := s.getAppArgs | return .continue
  -- The terms are built directly (no `mkAppM`): simp has already rewritten `c` but not
  -- the instance `inst`, which is only definitionally of type `Decidable c`.
  try
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
