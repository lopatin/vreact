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

/-- The code units of a literal string (as `reduceOfString` leaves it). -/
private def unitsLit? (e : Expr) : Option (List Nat) := do
  guard (e.isAppOfArity ``JS.Str.mk 1)
  let (_, xs) ← e.appArg!.listLit?
  xs.mapM fun x => match x.getAppFnArgs with
    | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => some n
    | _ => none

/-- `includes`/`startsWith`/`endsWith` of two literal strings are decided (`"a@b".includes("@")`):
the code-unit lists are compared as numbers (code units are below 2^16, so as `UInt16`s they
compare the same).  Definitional (`dsimproc`): the kernel re-checks it by evaluation. -/
dsimproc [vreact_simp] reduceStrIncludes (JS.strIncludes _ _) := fun e => do
  let_expr JS.strIncludes s t ← e | return .continue
  let (some a, some b) := (unitsLit? s, unitsLit? t) | return .continue
  return .done (toExpr (JS.isInfixB b a))
dsimproc [vreact_simp] reduceStartsWith (JS.startsWith _ _) := fun e => do
  let_expr JS.startsWith s t ← e | return .continue
  let (some a, some b) := (unitsLit? s, unitsLit? t) | return .continue
  return .done (toExpr (b.isPrefixOf a))
dsimproc [vreact_simp] reduceEndsWith (JS.endsWith _ _) := fun e => do
  let_expr JS.endsWith s t ← e | return .continue
  let (some a, some b) := (unitsLit? s, unitsLit? t) | return .continue
  return .done (toExpr (b.isSuffixOf a))

/-! ### Callbacks over `l.attach` that do not use the membership proof

A callback with proof obligations is translated over `l.attach` (`fun p => let x := p.1; have
hmem := p.2; …`), so that its obligations may use `x ∈ l`.  Once they are proved, the callback
usually does not depend on the proof any more; these simprocs then return to `l` itself
(`(l.attach.filter P).map (·.1)` ↦ `l.filter P'`), so the result is in the same form as the
facts about `l` (distinct keys, counts).  The core lemmas (`List.map_subtype`, …) need their
side condition `∀ x h, f ⟨x, h⟩ = ?g x` solved by `simp`, which our Bool normalisation breaks. -/

theorem map_attach_eq {α β} {l : List α} {f : {x // x ∈ l} → β} {g : α → β} (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    l.attach.map f = l.map g := by
  rw [← List.attach_map_val (f := g)]; exact List.map_congr_left fun ⟨x, h⟩ _ => hf x h
theorem map_filter_attach_eq {α β} {l : List α} {p : {x // x ∈ l} → Bool} {q : α → Bool}
    {f : {x // x ∈ l} → β} {g : α → β} (hp : ∀ x h, p ⟨x, h⟩ = q x) (hf : ∀ x h, f ⟨x, h⟩ = g x) :
    (l.attach.filter p).map f = (l.filter q).map g := by
  rw [List.map_subtype (g := g) hf, List.unattach_filter (hf := hp), List.unattach_attach]
theorem unattach_filter_attach_eq {α} {l : List α} {p : {x // x ∈ l} → Bool} {q : α → Bool}
    (hp : ∀ x h, p ⟨x, h⟩ = q x) : (l.attach.filter p).unattach = l.filter q := by
  rw [List.unattach_filter (hf := hp), List.unattach_attach]
theorem length_filter_attach_eq {α} {l : List α} {p : {x // x ∈ l} → Bool} {q : α → Bool}
    (hp : ∀ x h, p ⟨x, h⟩ = q x) : (l.attach.filter p).length = (l.filter q).length := by
  rw [← List.length_unattach, unattach_filter_attach_eq hp]
theorem all_attach_eq {α} {l : List α} {p : {x // x ∈ l} → Bool} {q : α → Bool}
    (hp : ∀ x h, p ⟨x, h⟩ = q x) : l.attach.all p = l.all q := by
  rw [List.all_subtype hp, List.unattach_attach]
theorem any_attach_eq {α} {l : List α} {p : {x // x ∈ l} → Bool} {q : α → Bool}
    (hp : ∀ x h, p ⟨x, h⟩ = q x) : l.attach.any p = l.any q := by
  rw [List.any_subtype hp, List.unattach_attach]

/-- For `f : {x // x ∈ l} → β` (a lambda, `l` its list) whose body uses its argument only through
`.1`: `(g, proof of ∀ x h, f ⟨x, h⟩ = g x)`. -/
private def dropAttach? (f : Expr) : MetaM (Option (Expr × Expr)) := do
  let .lam n ty body _ := f | return none
  let .const ``Subtype [u] := ty.getAppFn | return none
  let #[α, pr] := ty.getAppArgs | return none
  withLocalDeclD n α fun x => do
    withLocalDeclD `h (pr.beta #[x]) fun h => do
      let mk := mkApp4 (mkConst ``Subtype.mk [u]) α pr x h
      let b ← Meta.transform (body.instantiate1 mk) (post := fun e => do
        if e.isAppOfArity ``Subtype.val 3 && (e.getArg! 2).isAppOfArity ``Subtype.mk 4 then
          return .done ((e.getArg! 2).getArg! 2)
        if let .proj ``Subtype 0 a := e then
          if a.isAppOfArity ``Subtype.mk 4 then return .done (a.getArg! 2)
        return .continue)
      if b.containsFVar h.fvarId! then return none
      let g ← mkLambdaFVars #[x] b
      -- `f ⟨x, h⟩ = g x` holds by `rfl` (β, and `Subtype.val ⟨x, h⟩ ≡ x`)
      let lhs := f.beta #[mk]
      let pf ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs b)
      return some (g, ← mkLambdaFVars #[x, h] pf)

/-- `List.attach l` with its list. -/
private def attachOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``List.attach 2 then some (e.getArg! 1) else none

simproc [vreact_simp] reduceMapAttach (List.map _ _) := fun e => do
  let_expr List.map _ β f xs ← e | return .continue
  -- `(l.attach.filter p).map f`
  if xs.isAppOfArity ``List.filter 3 then
    let some l := attachOf? (xs.getArg! 2) | return .continue
    let p := xs.getArg! 1
    let some (q, hp) ← dropAttach? p | return .continue
    let some (g, hf) ← dropAttach? f | return .continue
    let pf ← mkAppOptM ``map_filter_attach_eq #[none, β, l, p, q, f, g, hp, hf]
    return .visit { expr := (← inferType pf).appArg!, proof? := some pf }
  let some l := attachOf? xs | return .continue
  let some (g, hf) ← dropAttach? f | return .continue
  let pf ← mkAppOptM ``map_attach_eq #[none, β, l, f, g, hf]
  return .visit { expr := (← inferType pf).appArg!, proof? := some pf }

simproc [vreact_simp] reduceUnattachFilterAttach (List.unattach _) := fun e => do
  let_expr List.unattach _ _ xs ← e | return .continue
  let_expr List.filter _ p la ← xs | return .continue
  let some l := attachOf? la | return .continue
  let some (q, hp) ← dropAttach? p | return .continue
  let pf ← mkAppOptM ``unattach_filter_attach_eq #[none, l, p, q, hp]
  return .visit { expr := (← inferType pf).appArg!, proof? := some pf }

simproc [vreact_simp] reduceLengthFilterAttach (List.length (List.filter _ _)) := fun e => do
  let_expr List.length _ xs ← e | return .continue
  let_expr List.filter _ p la ← xs | return .continue
  let some l := attachOf? la | return .continue
  let some (q, hp) ← dropAttach? p | return .continue
  let pf ← mkAppOptM ``length_filter_attach_eq #[none, l, p, q, hp]
  return .visit { expr := (← inferType pf).appArg!, proof? := some pf }

simproc [vreact_simp] reduceAllAttach (List.all _ _) := fun e => do
  let_expr List.all _ la p ← e | return .continue
  let some l := attachOf? la | return .continue
  let some (q, hp) ← dropAttach? p | return .continue
  let pf ← mkAppOptM ``all_attach_eq #[none, l, p, q, hp]
  return .visit { expr := (← inferType pf).appArg!, proof? := some pf }

simproc [vreact_simp] reduceAnyAttach (List.any _ _) := fun e => do
  let_expr List.any _ la p ← e | return .continue
  let some l := attachOf? la | return .continue
  let some (q, hp) ← dropAttach? p | return .continue
  let pf ← mkAppOptM ``any_attach_eq #[none, l, p, q, hp]
  return .visit { expr := (← inferType pf).appArg!, proof? := some pf }

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
