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

/-! ### Comparing strings: literal prefixes, integers

The keys of sibling elements are compared as strings (`VList.withKeys`): `key={`v-${id}`}` and
`key={`n-${id}`}` differ by their literal prefixes, `key={id}` and `key="title"` because the
decimal rendering of an integer has only digits and `-`, `key={i}` and `key={j}` exactly when
`i ≠ j`. -/

@[vreact_simp] theorem JS.Str.mk_nil_append (s : JS.Str) : (⟨[]⟩ : JS.Str) ++ s = s := rfl
@[vreact_simp] theorem JS.Str.append_mk_nil (s : JS.Str) : s ++ (⟨[]⟩ : JS.Str) = s := by
  cases s; exact congrArg JS.Str.mk (List.append_nil _)

/-- Two strings with literal prefixes (as `reduceOfString` leaves them) agree on their first code
units. -/
@[vreact_simp] theorem JS.Str.mk_cons_append_eq_mk_cons_append (x y : UInt16) (xs ys : List UInt16) (s t : JS.Str) :
    ((⟨x :: xs⟩ : JS.Str) ++ s = ⟨y :: ys⟩ ++ t) ↔ (x = y ∧ (⟨xs⟩ : JS.Str) ++ s = ⟨ys⟩ ++ t) := by
  cases s; cases t
  show JS.Str.mk _ = JS.Str.mk _ ↔ _ ∧ JS.Str.mk _ = JS.Str.mk _
  simp
@[vreact_simp] theorem JS.Str.mk_cons_append_eq_mk_cons (x y : UInt16) (xs ys : List UInt16) (s : JS.Str) :
    ((⟨x :: xs⟩ : JS.Str) ++ s = ⟨y :: ys⟩) ↔ (x = y ∧ (⟨xs⟩ : JS.Str) ++ s = ⟨ys⟩) := by
  cases s
  show JS.Str.mk _ = JS.Str.mk _ ↔ _ ∧ JS.Str.mk _ = JS.Str.mk _
  simp
@[vreact_simp] theorem JS.Str.mk_cons_eq_mk_cons_append (x y : UInt16) (xs ys : List UInt16) (t : JS.Str) :
    ((⟨x :: xs⟩ : JS.Str) = ⟨y :: ys⟩ ++ t) ↔ (x = y ∧ (⟨xs⟩ : JS.Str) = ⟨ys⟩ ++ t) := by
  cases t
  show JS.Str.mk _ = JS.Str.mk _ ↔ _ ∧ JS.Str.mk _ = JS.Str.mk _
  simp

namespace JS

/-- A code unit of the decimal rendering of an integer: a digit or `-`. -/
def intUnit (u : UInt16) : Bool := u == 45 || (48 ≤ u && u ≤ 57)

theorem toString_int_chars (a : Int) : ∀ c ∈ (toString a).toList, c = '-' ∨ c.isDigit = true := by
  intro c hc
  have hd : ∀ (n : Nat), ∀ c ∈ (Nat.repr n).toList, c.isDigit = true := by
    intro n c hc
    rw [Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  cases a with
  | ofNat m => exact Or.inr (hd m c hc)
  | negSucc m =>
    have : (toString (Int.negSucc m)).toList = '-' :: (Nat.repr (m + 1)).toList := by
      show ("-" ++ Nat.repr (m + 1)).toList = _
      rw [String.toList_append]; rfl
    rw [this] at hc
    rcases List.mem_cons.mp hc with h | h
    · exact Or.inl h
    · exact Or.inr (hd _ c h)

theorem toNat_lt_of_int_char (c : Char) (h : c = '-' ∨ c.isDigit = true) : c.toNat < 128 := by
  rcases h with h | h
  · subst h; decide
  · have : c.toNat ≤ 57 := by
      simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
      exact UInt32.le_iff_toNat_le.mp h.2
    omega

theorem flatMap_encodeChar_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) :
    l.flatMap Str.encodeChar = l.map (fun c => c.toNat.toUInt16) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.flatMap_cons, List.map_cons]
    have hc : c.val.toNat < 0x10000 := by have := h c (by simp); exact Nat.lt_trans this (by decide)
    rw [ih (fun c hc => h c (by simp [hc]))]
    simp only [Str.encodeChar, hc, ite_true]; rfl

theorem units_str_int (a : Int) : (str a).units = (toString a).toList.map (fun c => c.toNat.toUInt16) :=
  flatMap_encodeChar_ascii _ (fun c hc => toNat_lt_of_int_char c (toString_int_chars a c hc))

theorem map_toUInt16_inj (l1 l2 : List Char) (h1 : ∀ c ∈ l1, c.toNat < 128) (h2 : ∀ c ∈ l2, c.toNat < 128)
    (h : l1.map (fun c => c.toNat.toUInt16) = l2.map (fun c => c.toNat.toUInt16)) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons c l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons d l2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hc := h1 c (by simp)
      have hd := h2 d (by simp)
      have : c.toNat = d.toNat := by
        have := congrArg UInt16.toNat h.1
        simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat'] at this
        omega
      rw [Char.toNat_inj.mp this, ih l2 (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) h.2]

/-- `String(i) === String(j)` exactly when `i === j` (the decimal rendering is injective). -/
@[vreact_simp] theorem str_int_inj (a b : Int) : str a = str b ↔ a = b := by
  constructor
  · intro h
    have hu := congrArg Str.units h
    rw [units_str_int, units_str_int] at hu
    have := map_toUInt16_inj _ _ (fun c hc => toNat_lt_of_int_char c (toString_int_chars a c hc))
      (fun c hc => toNat_lt_of_int_char c (toString_int_chars b c hc)) hu
    exact Int.repr_inj.mp (String.toList_inj.mp this)
  · intro h; rw [h]

theorem intUnit_of_digit (n : Nat) (h1 : 48 ≤ n) (h2 : n ≤ 57) : intUnit n.toUInt16 = true := by
  have : ∀ n, n < 58 → 48 ≤ n → intUnit n.toUInt16 = true := by decide
  exact this n (by omega) h1

theorem str_int_units (a : Int) : (str a).units.all intUnit = true := by
  rw [units_str_int, List.all_eq_true]
  intro u hu
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
  rcases toString_int_chars a c hc with h | h
  · subst h; decide
  · simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
    exact intUnit_of_digit _ (UInt32.le_iff_toNat_le.mp h.1) (UInt32.le_iff_toNat_le.mp h.2)

theorem str_int_eq_lit (a : Int) (us : List UInt16) (h : us.all intUnit = false) : (str a = ⟨us⟩) = False := by
  apply _root_.eq_false; intro he
  have := str_int_units a
  rw [he] at this
  simp_all

theorem lit_eq_str_int (a : Int) (us : List UInt16) (h : us.all intUnit = false) : ((⟨us⟩ : Str) = str a) = False :=
  _root_.eq_false fun he => cast (str_int_eq_lit a us h) he.symm

/-- `x` starts with the decimal rendering of an integer: its first code unit is a digit or `-`. -/
def IntHead (x : Str) : Prop := ∃ c cs, x.units = c :: cs ∧ intUnit c = true

theorem intHead_str (a : Int) : IntHead (str a) := by
  have hne : (toString a).toList ≠ [] := by
    cases a with
    | ofNat m =>
      show (Nat.repr m).toList ≠ []
      rw [Nat.toList_repr]; exact Nat.toDigits_ne_nil
    | negSucc m =>
      show ("-" ++ Nat.repr (m + 1)).toList ≠ []
      rw [String.toList_append]; simp
  have hall := str_int_units a
  unfold IntHead
  rw [units_str_int] at hall ⊢
  cases h : (toString a).toList with
  | nil => exact absurd h hne
  | cons c cs =>
    rw [h] at hall
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hall
    exact ⟨_, _, rfl, hall.1⟩

theorem intHead_append (x s : Str) (h : IntHead x) : IntHead (x ++ s) := by
  obtain ⟨c, cs, hx, hc⟩ := h
  exact ⟨c, cs ++ s.units, by rw [Str.units_append, hx]; rfl, hc⟩

theorem eq_false_of_intHead (x y : Str) (hx : IntHead x) (u : UInt16) (hy : y.units.head? = some u)
    (hu : intUnit u = false) : (x = y) = False := by
  apply _root_.eq_false; intro he
  obtain ⟨c, cs, hxc, hc⟩ := hx
  rw [← he, hxc] at hy
  simp only [List.head?_cons, Option.some.injEq] at hy
  rw [hy] at hc; rw [hc] at hu; exact Bool.noConfusion hu

theorem eq_false_of_intHead' (x y : Str) (hy : IntHead y) (u : UInt16) (hx : x.units.head? = some u)
    (hu : intUnit u = false) : (x = y) = False :=
  _root_.eq_false fun he => cast (eq_false_of_intHead y x hy u hx hu) he.symm

end JS

/-- `String(i) === "abc"` for an integer `i` and a literal string with a code unit that is not a
digit or `-` (as `reduceOfString` leaves it): false (`JS.str_int_eq_lit`); also when only the first
code unit tells (`String(i) + s === "n" + t`, `JS.eq_false_of_intHead`).  The side conditions hold
by evaluation, which the kernel re-checks. -/
simproc [vreact_simp] reduceStrIntEqLit ((_ : JS.Str) = _) := fun e => do
  let_expr Eq _ l r ← e | return .continue
  let intOf? (x : Expr) : Option Expr :=
    if x.isAppOfArity ``JS.str 3 && (x.getArg! 0).isConstOf ``Int && (x.getArg! 1).isConstOf ``JS.instToJSInt then
      some (x.getArg! 2)
    else none
  let nonInt (us : List Nat) : Bool := us.any fun u => !(u == 45 || (48 ≤ u && u ≤ 57))
  let side ← mkEqRefl (mkConst ``Bool.false)
  if let (some a, some us) := (intOf? l, unitsLit? r) then
    if nonInt us then
      return .done { expr := mkConst ``False, proof? := some (mkApp3 (mkConst ``JS.str_int_eq_lit) a r.appArg! side) }
  if let (some us, some a) := (unitsLit? l, intOf? r) then
    if nonInt us then
      return .done { expr := mkConst ``False, proof? := some (mkApp3 (mkConst ``JS.lit_eq_str_int) a l.appArg! side) }
  -- `String(i) + s === "ab" + t` (either side, with or without the rest): the first code units
  let intHead? (x : Expr) : Option Expr :=
    if let some a := intOf? x then some (mkApp (mkConst ``JS.intHead_str) a)
    else if x.isAppOfArity ``HAppend.hAppend 6 then
      (intOf? (x.getArg! 4)).map fun a =>
        mkApp3 (mkConst ``JS.intHead_append) (x.getArg! 4) (x.getArg! 5) (mkApp (mkConst ``JS.intHead_str) a)
    else none
  let litHead? (x : Expr) : Option Nat := do
    let lit := if x.isAppOfArity ``HAppend.hAppend 6 then x.getArg! 4 else x
    let u :: _ ← unitsLit? lit | none
    some u
  let headProof (x : Expr) (u : Nat) : MetaM (Expr × Expr) := do
    let uE ← mkNumeral (mkConst ``UInt16) u
    let ty ← mkEq (← mkAppM ``List.head? #[← mkAppM ``JS.Str.units #[x]]) (← mkAppM ``Option.some #[uE])
    return (uE, ← mkExpectedTypeHint (← mkEqRefl (← mkAppM ``Option.some #[uE])) ty)
  let nonIntUnit (u : Nat) : Bool := !(u == 45 || (48 ≤ u && u ≤ 57))
  if let (some hx, some u) := (intHead? l, litHead? r) then
    if nonIntUnit u then
      let (uE, hy) ← headProof r u
      return .done { expr := mkConst ``False, proof? := some (mkAppN (mkConst ``JS.eq_false_of_intHead) #[l, r, hx, uE, hy, side]) }
  if let (some u, some hy) := (litHead? l, intHead? r) then
    if nonIntUnit u then
      let (uE, hx) ← headProof l u
      return .done { expr := mkConst ``False, proof? := some (mkAppN (mkConst ``JS.eq_false_of_intHead') #[l, r, hy, uE, hx, side]) }
  return .continue

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
