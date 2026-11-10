/-!
# VReact.JS — a model of the JavaScript runtime operations used by the VTS subset

Every TypeScript operation the translator accepts is mapped to a Lean definition
here (or to a core Lean operation with identical semantics).  The guiding rule:

* If an operation can throw or produce `undefined`/`NaN` in JS, the model either
  (a) returns an `Option`, or (b) takes a *proof obligation* that rules the bad
  case out (e.g. array indexing, `Array.prototype.with`, integer division).
* If JS semantics are too irregular to model faithfully (Unicode case mapping,
  float formatting) the operation is `opaque`: proofs may not rely on its result.
* Integers (`int`) are mathematical integers; we do not model the 2^53 limit.
* Numbers (`number`) are an opaque type `Num` with opaque operations (not Lean's
  `Float`, which the kernel can compute with and whose library differs from JS):
  proofs cannot compute or decide anything about them.
* Values are JS values up to the sign of zero (`-0` is `0`): the only accepted
  operation that tells them apart, a division by a zero, carries the obligation
  that its divisor is not zero (`Num.divInt`, `Num.divNum`).
* Strings are sequences of Unicode scalar values.  `length` is modelled exactly
  (UTF-16 code units); slicing works on code points, which coincides with JS for
  strings without astral characters (documented abstraction).
-/
namespace VReact.JS

/-! ## Strings

A JavaScript string *is* a finite sequence of UTF-16 code units (ECMA-262 §6.1.4).
We model exactly that, so `length`, `slice`, `===`, `includes`, `startsWith`,
`endsWith`, `trim`, concatenation and `repeat` are exact — including strings
with emoji (surrogate pairs) and even lone surrogates.  Only Unicode case
mapping is left opaque. -/

/-- A JavaScript string value. -/
structure Str where
  units : List UInt16
deriving DecidableEq, Repr, Inhabited

namespace Str

instance : Append Str := ⟨fun a b => ⟨a.units ++ b.units⟩⟩
@[simp] theorem units_append (a b : Str) : (a ++ b).units = a.units ++ b.units := rfl

/-- UTF-16 encoding of a Unicode scalar value (one or two code units). -/
def encodeChar (c : Char) : List UInt16 :=
  let v := c.val.toNat
  if v < 0x10000 then [v.toUInt16]
  else
    let w := v - 0x10000
    [(0xD800 + w / 0x400).toUInt16, (0xDC00 + w % 0x400).toUInt16]

/-- A string literal of the source program. -/
def ofString (s : String) : Str := ⟨s.toList.flatMap encodeChar⟩

@[simp] theorem ofString_empty : ofString "" = ⟨[]⟩ := rfl

end Str

/-- `s.length` (UTF-16 code units). -/
@[reducible] def strLen (s : Str) : Int := s.units.length

/-- JS `WhiteSpace ∪ LineTerminator` (ECMA-262 §12.2–12.3), the set `trim` removes.
All of them are BMP code points, i.e. single code units. -/
def isWS (u : UInt16) : Bool :=
  u == 0x09 || u == 0x0A || u == 0x0B || u == 0x0C || u == 0x0D || u == 0x20 ||
  u == 0xA0 || u == 0x1680 || (0x2000 ≤ u && u ≤ 0x200A) || u == 0x2028 || u == 0x2029 ||
  u == 0x202F || u == 0x205F || u == 0x3000 || u == 0xFEFF

/-- `s.trim()` -/
def trim (s : Str) : Str := ⟨((s.units.dropWhile isWS).reverse.dropWhile isWS).reverse⟩

def isInfixB {α} [BEq α] (p : List α) : List α → Bool
  | [] => p.isPrefixOf []
  | s@(_ :: t) => p.isPrefixOf s || isInfixB p t

/-- `s.includes(t)` -/
def strIncludes (s t : Str) : Bool := isInfixB t.units s.units
/-- `s.startsWith(t)` -/
def startsWith (s t : Str) : Bool := t.units.isPrefixOf s.units
/-- `s.endsWith(t)` -/
def endsWith (s t : Str) : Bool := t.units.isSuffixOf s.units

/-- Unicode case mapping is not modelled: opaque. -/
opaque toLowerCase : Str → Str
opaque toUpperCase : Str → Str

/-- `s.repeat(n)` (requires `n ≥ 0`, otherwise JS throws RangeError). -/
def strRepeat (s : Str) (n : Int) (_h : 0 ≤ n) : Str := ⟨(List.replicate n.toNat s.units).flatten⟩

/-! ## Conversion to string (template literals, `String(x)`, JSX text) -/

class ToJS (α : Type) where
  str : α → Str

instance : ToJS Str := ⟨id⟩
/-- Lean's decimal rendering of `Int` coincides with JS `String(n)` for safe integers. -/
instance : ToJS Int := ⟨fun i => Str.ofString (toString i)⟩
instance : ToJS Nat := ⟨fun i => Str.ofString (toString i)⟩
instance : ToJS Bool := ⟨fun b => if b then Str.ofString "true" else Str.ofString "false"⟩

def str {α} [ToJS α] (a : α) : Str := ToJS.str a

/-! ## Integers (the `int` type of VTS) -/

/-- `a % b` on integers (ECMA-262 Number::remainder): the result has the sign of
the dividend and magnitude `|a| mod |b|`.  (`%` below is Lean's Euclidean `emod`.) -/
def rem (a b : Int) (_h : b ≠ 0) : Int :=
  if 0 ≤ a then a % (b.natAbs : Int) else -((-a) % (b.natAbs : Int))
/-- The range of `a % b` (ECMA remainder, the sign of the dividend): `0 ≤ r < |b|` for
`a ≥ 0`, `-|b| < r ≤ 0` for `a < 0`.  A contract (`f.post`, see `vreact_contracts`), so the
facts are in the context of every goal with a `%`, also for `omega`. -/
theorem rem.post (a b : Int) (h : b ≠ 0) :
    (0 ≤ a → 0 ≤ rem a b h ∧ rem a b h < (b.natAbs : Int)) ∧
    (a < 0 → -(b.natAbs : Int) < rem a b h ∧ rem a b h ≤ 0) := by
  have h1 : (0 : Int) < (b.natAbs : Int) := by omega
  unfold rem
  constructor
  · intro ha; simp only [ha, if_true]
    exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ h1⟩
  · intro ha; simp only [show ¬ 0 ≤ a by omega, if_false]
    have := Int.emod_nonneg (-a) (b := (b.natAbs : Int)) (by omega)
    have := Int.emod_lt_of_pos (-a) h1
    omega
/-- The exact values of `a % b` that index arithmetic needs (a contract like `rem.post`): `a`
itself when `|a| < |b|` with the sign of `a` (`(sel + 1) % n === sel + 1` for `sel + 1 < n`), and
`0` for `a = ±b` (`n % n === 0`: the step from the last slide to the first). -/
theorem rem.post2 (a b : Int) (h : b ≠ 0) :
    (0 ≤ a → a < (b.natAbs : Int) → rem a b h = a) ∧
    (-(b.natAbs : Int) < a → a ≤ 0 → rem a b h = a) ∧
    (a = b ∨ a = -b → rem a b h = 0) := by
  unfold rem
  refine ⟨fun h0 h1 => ?_, fun h0 h1 => ?_, fun hab => ?_⟩
  · rw [if_pos h0]; exact Int.emod_eq_of_lt h0 h1
  · by_cases ha : 0 ≤ a
    · have : a = 0 := by omega
      subst this; simp
    · rw [if_neg ha, Int.emod_eq_of_lt (by omega) (by omega)]; omega
  · have hd : (b.natAbs : Int) ∣ a := by
      rw [Int.natAbs_dvd]
      rcases hab with rfl | rfl
      · exact Int.dvd_refl _
      · exact (Int.dvd_neg).2 (Int.dvd_refl _)
    have hd' : (b.natAbs : Int) ∣ -a := (Int.dvd_neg).2 hd
    split
    · exact Int.emod_eq_zero_of_dvd hd
    · rw [Int.emod_eq_zero_of_dvd hd']; rfl
/-- `%` with a variable divisor: `grind` decides `%` by a numeral only, so it gets the range of
`emod` (which `rem` unfolds to) for every `a % b`. -/
theorem emod_nonneg_of_ne (a b : Int) (h : b ≠ 0) : 0 ≤ a % b := Int.emod_nonneg a h
theorem emod_lt_of_pos (a b : Int) (h : 0 < b) : a % b < b := Int.emod_lt_of_pos a h
grind_pattern emod_nonneg_of_ne => a % b
grind_pattern emod_lt_of_pos => a % b
/-- The exact values (`rem.post2` for `emod`, which `rem` unfolds to): `a % b = a` for `0 ≤ a <
b`, and `a % |a| = 0` (E-matching modulo equalities also finds `(sel + 1) % |n|` when `sel + 1 = n`). -/
theorem emod_eq_self_of_lt (a b : Int) (h0 : 0 ≤ a) (h1 : a < b) : a % b = a := Int.emod_eq_of_lt h0 h1
theorem emod_natAbs_self (a : Int) : a % (a.natAbs : Int) = 0 :=
  Int.emod_eq_zero_of_dvd (Int.natAbs_dvd.2 (Int.dvd_refl a))
grind_pattern emod_eq_self_of_lt => a % b
grind_pattern emod_natAbs_self => a % (a.natAbs : Int)

/-- `Math.floor(a / b)` on integers. (Lean's `/` on `Int` rounds toward −∞ for positive divisors.) -/
def floorDiv (a b : Int) (_h : b ≠ 0) : Int := if 0 < b then a / b else (-a) / (-b)
/-- `Math.trunc(a / b)` on integers. -/
def truncDiv (a b : Int) (_h : b ≠ 0) : Int :=
  if (0 ≤ a) = (0 < b) then ((a.natAbs / b.natAbs : Nat) : Int) else -((a.natAbs / b.natAbs : Nat) : Int)
/-- `Math.abs` -/
def abs (a : Int) : Int := if a < 0 then -a else a
/-- `Math.sign` -/
def sign (a : Int) : Int := if a < 0 then -1 else if a = 0 then 0 else 1

/-! ## Numbers (the `number` type of VTS): opaque to proofs

A JS number is an IEEE-754 double. Lean's `Float` is not used for them: the kernel can
compute with it (Lean has a model of `Float`: `decide` proves facts about float arithmetic
and literals), and its library is not JavaScript's (`max` is `maxOfLe`, so `max 1 NaN = 1`
where `Math.max(1, NaN)` is NaN; `Float.round` rounds half-way cases away from zero,
`Math.round` towards +∞; …). VTS numbers are the type `Num`, and every operation on them
— literals, arithmetic, comparisons, `===`, `Math.*`, conversion to a string — is an opaque
constant: the kernel never unfolds them, so a proof can use hypotheses and congruence about
numbers but can neither compute nor decide anything about them. In particular `===` is the
uninterpreted IEEE test `Num.eq` (not reflexive: `NaN !== NaN`), and nothing relates
`Num.lt`, `Num.le` and `Num.eq`. No axioms: these are `opaque` definitions (of a nonempty
type, through `Classical.choice`), so they are noncomputable — Lean never runs the app. -/

/-- The representation of JS numbers: some nonempty type, nothing else is known. -/
opaque NumRepr : NonemptyType.{0}

/-- A JS `number` (IEEE-754 double). -/
def Num : Type := NumRepr.type

instance : Nonempty Num := NumRepr.property

namespace Num
/-- An `int` as a number (an int-valued number is the same JS value). -/
noncomputable opaque ofInt : Int → Num
/-- A numeric literal `m × 10^(±e)` (Lean's `OfScientific`): the double JS reads it as. -/
noncomputable opaque ofScientific : Nat → Bool → Nat → Num
/-- `a + b` -/
noncomputable opaque add : Num → Num → Num
/-- `a - b` -/
noncomputable opaque sub : Num → Num → Num
/-- `a * b` -/
noncomputable opaque mul : Num → Num → Num
/-- `a / b` -/
noncomputable opaque div : Num → Num → Num
/-- `-a` -/
noncomputable opaque neg : Num → Num
/-- `a < b` (false when either is NaN) -/
noncomputable opaque lt : Num → Num → Bool
/-- `a <= b` (false when either is NaN) -/
noncomputable opaque le : Num → Num → Bool
/-- `a === b`: IEEE equality (`NaN !== NaN`, `0 === -0`) -/
noncomputable opaque eq : Num → Num → Bool
/-- `Math.floor` -/
noncomputable opaque floor : Num → Num
/-- `Math.ceil` -/
noncomputable opaque ceil : Num → Num
/-- `Math.round` (half-way cases towards +∞) -/
noncomputable opaque round : Num → Num
/-- `Math.trunc` -/
noncomputable opaque trunc : Num → Num
/-- `Math.abs` -/
noncomputable opaque abs : Num → Num
/-- `Math.max(a, b)` (NaN if either is NaN; `+0` above `-0`) -/
noncomputable opaque max : Num → Num → Num
/-- `Math.min(a, b)` -/
noncomputable opaque min : Num → Num → Num
/-- `String(a)` (Number::toString, shortest round-trip form) -/
noncomputable opaque toStr : Num → Str
end Num

noncomputable instance (n : Nat) : OfNat Num n := ⟨Num.ofInt n⟩
noncomputable instance : OfScientific Num := ⟨Num.ofScientific⟩
noncomputable instance : Add Num := ⟨Num.add⟩
noncomputable instance : Sub Num := ⟨Num.sub⟩
noncomputable instance : Mul Num := ⟨Num.mul⟩
noncomputable instance : Div Num := ⟨Num.div⟩
noncomputable instance : Neg Num := ⟨Num.neg⟩
noncomputable instance : ToJS Num := ⟨Num.toStr⟩
/-- (Generated records derive `Repr`; a number is not printed.) -/
instance : Repr Num := ⟨fun _ _ => "«number»"⟩

/-! ### Division: a divisor that is not zero

VTS values are JS values *up to the sign of zero*: an `int` that is 0 may be `-0` in JS (`-x`,
`a * b`, `a % b`, `Math.trunc(a / b)`, `Math.floor(0 / -5)`, `Math.min(0, -0)` give `-0`), Lean's
`Int` has one zero, and `Num.ofInt` maps it to one number. Every operation VTS accepts gives
equal results (up to the sign of zero) for `0` and `-0` — comparisons and `===` (`-0 === 0`),
`+ - *`, unary `-`, `Math.*`, `String(x)`, indexing — except a division *by* a zero: `1 / 0` is
`Infinity`, `1 / -0` is `-Infinity`. So a number division carries the obligation that its divisor
is not zero (as an int: `b ≠ 0`; as a number: `b !== 0`, i.e. neither `0` nor `-0`; a nonzero
literal divisor needs none), and then the Lean term denotes the JS value. -/

/-- `a / b` with an int divisor `b ≠ 0`. -/
noncomputable def Num.divInt (a : Num) (b : Int) (_h : b ≠ 0) : Num := a / Num.ofInt b
/-- `a / b` with a number divisor that is not zero (`b !== 0`: neither `0` nor `-0`; the
literal `0` as the translation writes it, `Num.ofInt 0`). -/
noncomputable def Num.divNum (a b : Num) (_h : Num.eq b (Num.ofInt 0) = false) : Num := a / b

/-! ## Arrays (immutable `readonly T[]`, modelled as `List`) -/

/-- `xs.length` -/
@[reducible] def len {α} (xs : List α) : Int := xs.length

/-- Resolve a relative index the way `slice` does. -/
def relIndex (n : Int) (k : Int) : Nat := (if k < 0 then max (n + k) 0 else min k n).toNat

/-- `xs[i]` — JS returns `undefined` out of range, so VTS demands a bounds proof. -/
@[reducible] def get {α} (xs : List α) (i : Int) (h : 0 ≤ i ∧ i < xs.length) : α := xs[i.toNat]'(by omega)

@[simp] theorem get_eq {α} (xs : List α) (i : Int) (h : 0 ≤ i ∧ i < xs.length) :
    get xs i h = xs[i.toNat]'(by omega) := rfl

theorem get_mem {α} (xs : List α) (i : Int) (h : 0 ≤ i ∧ i < xs.length) : get xs i h ∈ xs := by
  simp [get]

/-- `[lo, lo+1, …, hi-1]` (bounded quantifiers `forall`/`exists` iterate over it). -/
def rangeFrom (lo hi : Int) : List Int := (List.range (hi - lo).toNat).map (fun (k : Nat) => lo + k)

theorem mem_rangeFrom (lo hi i : Int) : i ∈ rangeFrom lo hi ↔ lo ≤ i ∧ i < hi := by
  simp only [rangeFrom, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨(i - lo).toNat, by omega, by omega⟩

/-- `xs.slice(start, end?)` with full JS negative-index clamping semantics. -/
def slice {α} (xs : List α) (start : Int) (stop : Option Int := none) : List α :=
  let n : Int := xs.length
  let s := relIndex n start
  let e := match stop with | none => xs.length | some k => relIndex n k
  (xs.drop s).take (e - s)

/-- `s.slice(start, end?)` on strings: slicing code units, exactly as JS. -/
def strSlice (s : Str) (start : Int) (stop : Option Int := none) : Str :=
  ⟨slice s.units start stop⟩

/-- `xs.findIndex(p)` -/
def findIndex {α} (xs : List α) (p : α → Bool) : Int :=
  match xs.findIdx? p with
  | some i => i
  | none => -1

/-- `xs.indexOf(x)` (strict equality on primitive-like values) -/
def indexOf {α} [BEq α] (xs : List α) (x : α) : Int := findIndex xs (· == x)

/-- `xs.at(i)`: negative indices count from the end; out of range gives `undefined`. -/
def atOpt {α} (xs : List α) (i : Int) : Option α :=
  let k := if i < 0 then (xs.length : Int) + i else i
  if 0 ≤ k then xs[k.toNat]? else none

/-- `xs.with(i, v)` (ES2023): throws RangeError when out of range, hence the obligation. (A
negative index counts from the end in JS: VTS reads one written `-k` as `withEnd`, and requires
`0 ≤ i` of any other.) -/
def withAt {α} (xs : List α) (i : Int) (v : α) (_h : 0 ≤ i ∧ i < xs.length) : List α :=
  xs.set i.toNat v

/-- `xs.with(-k, v)` with `k > 0`: a negative index counts from the end, ES2023 writes at
`xs.length - k` and throws RangeError unless `-xs.length ≤ -k`, hence the obligation. -/
def withEnd {α} (xs : List α) (k : Int) (v : α) (_h : 0 < k ∧ k ≤ xs.length) : List α :=
  xs.set (xs.length - k).toNat v

/-- ECMA-262 (SortIndexedProperties): `cmp` is a *consistent comparator* for the
elements of `xs` — reflexive and symmetric `=`, transitive `=`, `<` and `>`. -/
def Consistent {α} (cmp : α → α → Int) (xs : List α) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, ∀ c ∈ xs,
    cmp a a = 0 ∧ (cmp a b = 0 → cmp b a = 0) ∧
    (cmp a b = 0 → cmp b c = 0 → cmp a c = 0) ∧
    (cmp a b < 0 → cmp b c < 0 → cmp a c < 0) ∧
    (0 < cmp a b → 0 < cmp b c → 0 < cmp a c)

instance {α} (cmp : α → α → Int) (xs : List α) : Decidable (Consistent cmp xs) := by
  unfold Consistent; infer_instance

/-- The order an engine produces for a comparator that is *not* consistent: ECMA-262
leaves it implementation-defined, so the model only knows it is a permutation (an
unspecified function of the list and the comparator). -/
noncomputable def unspecifiedSort {α} : List α → (α → α → Int) → List α :=
  Classical.choose (⟨fun xs _ => xs, fun _ _ => List.Perm.refl _⟩ :
    ∃ f : List α → (α → α → Int) → List α, ∀ xs cmp, (f xs cmp).Perm xs)

theorem unspecifiedSort_perm {α} (xs : List α) (cmp : α → α → Int) : (unspecifiedSort xs cmp).Perm xs :=
  Classical.choose_spec (⟨fun xs _ => xs, fun _ _ => List.Perm.refl _⟩ :
    ∃ f : List α → (α → α → Int) → List α, ∀ xs cmp, (f xs cmp).Perm xs) xs cmp

/-- `xs.toSorted(cmp)`. For a consistent comparator ECMA-262 fixes the result: the stable
sort (`a` stays before `b` when `cmp(a, b) ≤ 0`). Otherwise the order is
implementation-defined (V8 and Lean's merge sort differ), and the model only promises a
permutation. -/
noncomputable def toSorted {α} (xs : List α) (cmp : α → α → Int) : List α :=
  if Consistent cmp xs then xs.mergeSort (fun a b => decide (cmp a b ≤ 0)) else unspecifiedSort xs cmp

/-- `xs.join(sep)` -/
def join (xs : List Str) (sep : Str) : Str := ⟨sep.units.intercalate (xs.map (·.units))⟩

/-- `Array.from({ length: n }, (_, i) => f(i))` / the `range` helper. -/
def range (n : Int) : List Int := (List.range n.toNat).map (fun (i : Nat) => (i : Int))

/-- Keys of a keyed list must be pairwise distinct (React reconciliation requirement). -/
def distinct {α β} (xs : List α) (key : α → β) : Prop := (xs.map key).Nodup

/-! ## Boolean comparisons

Generated code compares with these instance-free functions rather than
`decide (a < b)`: simp may then rewrite the arguments (e.g. unfold a function
call) without leaving a stale `Decidable` instance behind. -/

def lt {α} [LT α] [DecidableLT α] (a b : α) : Bool := decide (a < b)
def le {α} [LE α] [DecidableLE α] (a b : α) : Bool := decide (a ≤ b)
def eq {α} [DecidableEq α] (a b : α) : Bool := decide (a = b)
def nodupB {α} [DecidableEq α] (xs : List α) : Bool := decide xs.Nodup

@[simp] theorem lt_iff {α} [LT α] [DecidableLT α] (a b : α) : lt a b = true ↔ a < b := decide_eq_true_iff
@[simp] theorem le_iff {α} [LE α] [DecidableLE α] (a b : α) : le a b = true ↔ a ≤ b := decide_eq_true_iff
@[simp] theorem eq_iff {α} [DecidableEq α] (a b : α) : eq a b = true ↔ a = b := decide_eq_true_iff
@[simp] theorem nodupB_iff {α} [DecidableEq α] (xs : List α) : nodupB xs = true ↔ xs.Nodup := decide_eq_true_iff
@[simp] theorem lt_false {α} [LT α] [DecidableLT α] (a b : α) : lt a b = false ↔ ¬ a < b := by simp [lt]
@[simp] theorem le_false {α} [LE α] [DecidableLE α] (a b : α) : le a b = false ↔ ¬ a ≤ b := by simp [le]
@[simp] theorem eq_false {α} [DecidableEq α] (a b : α) : eq a b = false ↔ a ≠ b := by simp [eq]
@[simp] theorem nodupB_false {α} [DecidableEq α] (xs : List α) : nodupB xs = false ↔ ¬ xs.Nodup := by simp [nodupB]

attribute [grind =] lt_iff le_iff eq_iff nodupB_iff lt_false le_false eq_false nodupB_false

/-! ## Lemmas for automation -/

@[simp] theorem len_nonneg {α} (xs : List α) : 0 ≤ len xs := by simp [len]
@[simp] theorem len_eq {α} (xs : List α) : len xs = (xs.length : Int) := rfl
@[simp] theorem len_nil {α} : len ([] : List α) = 0 := rfl
@[simp] theorem range_length (n : Int) : (range n).length = n.toNat := by simp [range]
theorem mem_range (n i : Int) : i ∈ range n ↔ 0 ≤ i ∧ i < n := by
  simp only [range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨i.toNat, by omega, by omega⟩

@[simp] theorem strLen_eq (s : Str) : strLen s = (s.units.length : Int) := rfl
@[simp] theorem strLen_nonneg (s : Str) : 0 ≤ strLen s := by simp [strLen]
@[simp] theorem strLen_empty : strLen (Str.ofString "") = 0 := rfl

theorem trim_units_length_le (s : Str) : (trim s).units.length ≤ s.units.length := by
  simp only [trim, List.length_reverse]
  have h1 := (List.dropWhile_suffix (p := isWS) (l := s.units)).length_le
  have h2 := (List.dropWhile_suffix (p := isWS) (l := (s.units.dropWhile isWS).reverse)).length_le
  simp only [List.length_reverse] at h2
  omega
grind_pattern trim_units_length_le => trim s

@[simp] theorem slice_length {α} (xs : List α) (a : Int) (b : Option Int) :
    (slice xs a b).length = (match b with | none => xs.length | some k => relIndex xs.length k) - relIndex xs.length a := by
  unfold slice relIndex
  cases b <;> simp <;> omega

theorem findIndex_bounds {α} (xs : List α) (p : α → Bool) :
    findIndex xs p = -1 ∨ (0 ≤ findIndex xs p ∧ findIndex xs p < xs.length) := by
  unfold findIndex
  split
  · rename_i i h
    right
    have := List.findIdx?_eq_some_iff_findIdx_eq.mp h
    omega
  · left; rfl

theorem findIndex_spec {α} (xs : List α) (p : α → Bool) (h : 0 ≤ findIndex xs p) :
    ∃ hlt : (findIndex xs p).toNat < xs.length, p (xs[(findIndex xs p).toNat]'hlt) = true := by
  unfold findIndex at *
  split at *
  · rename_i i hi
    have h1 := List.findIdx?_eq_some_iff_findIdx_eq.mp hi
    obtain ⟨hlt, heq⟩ := h1
    subst heq
    refine ⟨by simpa using hlt, ?_⟩
    simpa using List.findIdx_getElem (w := hlt)
  · simp at h

grind_pattern get_mem => get xs i h
grind_pattern findIndex_bounds => findIndex xs p

theorem findIndex_eq_neg_one_iff {α} (xs : List α) (p : α → Bool) :
    findIndex xs p = -1 ↔ ∀ x ∈ xs, p x = false := by
  unfold findIndex
  split
  · rename_i i h
    simp only [List.findIdx?_eq_some_iff_getElem] at h
    obtain ⟨hlt, hp, -⟩ := h
    constructor
    · intro h; omega
    · intro h'; have := h' _ (List.getElem_mem hlt); simp_all
  · rename_i h
    simpa using h
grind_pattern findIndex_eq_neg_one_iff => findIndex xs p

/-! ### `indexOf`: the facts of `findIndex`, plus what the found index points to -/

theorem indexOf_bounds {α} [BEq α] (xs : List α) (x : α) :
    indexOf xs x = -1 ∨ (0 ≤ indexOf xs x ∧ indexOf xs x < xs.length) := findIndex_bounds _ _
grind_pattern indexOf_bounds => indexOf xs x

theorem indexOf_eq_neg_one_iff {α} [BEq α] [LawfulBEq α] (xs : List α) (x : α) :
    indexOf xs x = -1 ↔ x ∉ xs := by
  unfold indexOf; rw [findIndex_eq_neg_one_iff]
  constructor
  · intro h hx; have := h x hx; simp at this
  · intro h y hy; simp only [beq_eq_false_iff_ne, ne_eq]; rintro rfl; exact h hy
grind_pattern indexOf_eq_neg_one_iff => indexOf xs x

theorem getElem_indexOf {α} [BEq α] [LawfulBEq α] (xs : List α) (x : α) (h0 : 0 ≤ indexOf xs x)
    (h : (indexOf xs x).toNat < xs.length) : xs[(indexOf xs x).toNat] = x := by
  obtain ⟨_, hp⟩ := findIndex_spec xs (· == x) h0
  simpa [indexOf] using hp
grind_pattern getElem_indexOf => xs[(indexOf xs x).toNat]

/-- `findIndex` of a concatenation: in the first part, else shifted in the second. -/
theorem findIndex_append {α} (l r : List α) (p : α → Bool) :
    findIndex (l ++ r) p = if l.any p then findIndex l p else if r.any p then l.length + findIndex r p else -1 := by
  have hl := @List.findIdx?_isSome _ l p
  have hr := @List.findIdx?_isSome _ r p
  unfold findIndex
  rw [List.findIdx?_append]
  cases h1 : l.findIdx? p with
  | some i =>
    have hl' : l.any p = true := by simpa [h1] using hl.symm
    simp [hl']
  | none =>
    have hl' : l.any p = false := by simpa [h1] using hl.symm
    cases h2 : r.findIdx? p with
    | some j =>
      have hr' : r.any p = true := by simpa [h2] using hr.symm
      simp [hl', hr']; omega
    | none =>
      have hr' : r.any p = false := by simpa [h2] using hr.symm
      simp [hl', hr']

/-- `indexOf` of a concatenation (e.g. the keys of a Map after appending a new key). -/
theorem indexOf_append {α} [BEq α] [LawfulBEq α] (l r : List α) (x : α) :
    indexOf (l ++ r) x = if x ∈ l then indexOf l x else if x ∈ r then l.length + indexOf r x else -1 := by
  unfold indexOf; rw [findIndex_append]; simp [List.any_eq_true]

theorem indexOf_singleton_self {α} [BEq α] [LawfulBEq α] (x : α) : indexOf [x] x = 0 := by
  simp [indexOf, findIndex]
attribute [grind =] indexOf_append indexOf_singleton_self

theorem getElem_findIndex {α} (xs : List α) (p : α → Bool) (h0 : 0 ≤ findIndex xs p)
    (h : (findIndex xs p).toNat < xs.length) : p xs[(findIndex xs p).toNat] = true := by
  obtain ⟨_, hp⟩ := findIndex_spec xs p h0
  exact hp
grind_pattern getElem_findIndex => xs[(findIndex xs p).toNat]

theorem findIndex_nonneg_iff {α} (xs : List α) (p : α → Bool) :
    0 ≤ findIndex xs p ↔ ∃ x ∈ xs, p x = true := by
  have hb := findIndex_bounds xs p
  have he := findIndex_eq_neg_one_iff xs p
  constructor
  · intro h
    have : ¬ findIndex xs p = -1 := by omega
    rw [he] at this
    simpa using this
  · rintro ⟨x, hx, hp⟩
    have : ¬ findIndex xs p = -1 := by rw [he]; intro h; simp [h x hx] at hp
    omega
grind_pattern findIndex_nonneg_iff => findIndex xs p

theorem indexOf_nonneg_iff {α} [BEq α] [LawfulBEq α] (xs : List α) (x : α) :
    0 ≤ indexOf xs x ↔ x ∈ xs := by
  have hb := indexOf_bounds xs x
  have he := indexOf_eq_neg_one_iff xs x
  constructor
  · intro h; exact Classical.byContradiction fun hx => by have := he.mpr hx; omega
  · intro hx; have : ¬ indexOf xs x = -1 := fun h => he.mp h hx
    omega
grind_pattern indexOf_nonneg_iff => indexOf xs x

/-- The range of `findIndex`/`indexOf` as contracts (`f.post`, see `vreact_contracts`): they
are added as hypotheses for every call in a goal, so `omega` and `simp_all` know them too,
not only `grind` (through the patterns above). -/
theorem findIndex.post {α} (xs : List α) (p : α → Bool) :
    -1 ≤ findIndex xs p ∧ findIndex xs p < xs.length := by
  rcases findIndex_bounds xs p with h | h <;> omega
theorem indexOf.post {α} [BEq α] (xs : List α) (x : α) :
    -1 ≤ indexOf xs x ∧ indexOf xs x < xs.length := findIndex.post _ _

/-! ### `with` keeps the length; reading back what was written -/

@[simp] theorem withAt_eq_set {α} (xs : List α) (i : Int) (v : α) (h : 0 ≤ i ∧ i < xs.length) :
    withAt xs i v h = xs.set i.toNat v := rfl
@[simp] theorem length_withAt {α} (xs : List α) (i : Int) (v : α) (h : 0 ≤ i ∧ i < xs.length) :
    (withAt xs i v h).length = xs.length := by simp
attribute [grind =] length_withAt
@[simp] theorem withEnd_eq_set {α} (xs : List α) (k : Int) (v : α) (h : 0 < k ∧ k ≤ xs.length) :
    withEnd xs k v h = xs.set (xs.length - k).toNat v := rfl
@[simp] theorem length_withEnd {α} (xs : List α) (k : Int) (v : α) (h : 0 < k ∧ k ≤ xs.length) :
    (withEnd xs k v h).length = xs.length := by simp
attribute [grind =] length_withEnd

/-! A swap `xs.with(i, xs[j]).with(j, xs[i])` is a permutation (`List.set_set_perm`): keys stay
distinct, membership and counts are unchanged. -/
@[simp, grind =] theorem nodup_map_set_swap {α β} (f : α → β) (xs : List α) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (((xs.set i xs[j]).set j xs[i]).map f).Nodup ↔ (xs.map f).Nodup :=
  ((List.set_set_perm hi hj).map f).nodup_iff
@[simp, grind =] theorem nodup_set_swap {α} (xs : List α) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Nodup ↔ xs.Nodup :=
  (List.set_set_perm hi hj).nodup_iff
@[simp, grind =] theorem mem_set_swap {α} (xs : List α) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) (a : α) :
    a ∈ (xs.set i xs[j]).set j xs[i] ↔ a ∈ xs :=
  (List.set_set_perm hi hj).mem_iff
@[simp, grind =] theorem length_filter_set_swap {α} (p : α → Bool) (xs : List α) (i j : Nat)
    (hi : i < xs.length) (hj : j < xs.length) :
    (((xs.set i xs[j]).set j xs[i]).filter p).length = (xs.filter p).length :=
  ((List.set_set_perm hi hj).filter p).length_eq

/-! ### `slice` is a sublist: membership and distinct keys carry over (chains of operations:
`SubPerm` in `Lists.lean`) -/

theorem slice_sublist {α} (xs : List α) (a : Int) (b : Option Int) : (slice xs a b).Sublist xs := by
  unfold slice; exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
@[grind →] theorem mem_of_mem_slice {α} {xs : List α} {a : Int} {b : Option Int} {x : α}
    (h : x ∈ slice xs a b) : x ∈ xs := (slice_sublist xs a b).subset h
theorem nodup_map_slice {α β} (f : α → β) (xs : List α) (a : Int) (b : Option Int) (h : (xs.map f).Nodup) :
    ((slice xs a b).map f).Nodup := h.sublist ((slice_sublist xs a b).map f)
grind_pattern nodup_map_slice => (slice xs a b).map f, (xs.map f).Nodup
theorem nodup_slice {α} (xs : List α) (a : Int) (b : Option Int) (h : xs.Nodup) : (slice xs a b).Nodup :=
  h.sublist (slice_sublist xs a b)
grind_pattern nodup_slice => slice xs a b, xs.Nodup
theorem length_filter_slice_le {α} (p : α → Bool) (xs : List α) (a : Int) (b : Option Int) :
    ((slice xs a b).filter p).length ≤ (xs.filter p).length := ((slice_sublist xs a b).filter p).length_le
grind_pattern length_filter_slice_le => (slice xs a b).filter p, xs.filter p

/-! ### `range(n)` has distinct elements -/

@[simp] theorem nodup_range (n : Int) : (range n).Nodup := by
  unfold range
  exact List.Pairwise.map (fun (i : Nat) => (i : Int)) (fun a b h h' => h (by omega)) List.nodup_range

/-! ### `toSorted`: a permutation; for a consistent comparator, the stable sort -/

theorem toSorted_perm {α} (xs : List α) (cmp : α → α → Int) : (toSorted xs cmp).Perm xs := by
  unfold toSorted; split
  · exact List.mergeSort_perm _ _
  · exact unspecifiedSort_perm _ _

@[simp, grind =] theorem length_toSorted {α} (xs : List α) (cmp : α → α → Int) :
    (toSorted xs cmp).length = xs.length := (toSorted_perm xs cmp).length_eq
@[simp, grind =] theorem mem_toSorted {α} (xs : List α) (cmp : α → α → Int) (a : α) :
    a ∈ toSorted xs cmp ↔ a ∈ xs := (toSorted_perm xs cmp).mem_iff
@[simp, grind =] theorem nodup_map_toSorted {α β} (xs : List α) (cmp : α → α → Int) (f : α → β) :
    ((toSorted xs cmp).map f).Nodup ↔ (xs.map f).Nodup := ((toSorted_perm xs cmp).map f).nodup_iff
@[simp, grind =] theorem nodup_toSorted {α} (xs : List α) (cmp : α → α → Int) :
    (toSorted xs cmp).Nodup ↔ xs.Nodup := (toSorted_perm xs cmp).nodup_iff
@[simp, grind =] theorem length_filter_toSorted {α} (xs : List α) (cmp : α → α → Int) (p : α → Bool) :
    ((toSorted xs cmp).filter p).length = (xs.filter p).length := ((toSorted_perm xs cmp).filter p).length_eq
@[simp] theorem toSorted_nil {α} (cmp : α → α → Int) : toSorted [] cmp = [] := (toSorted_perm [] cmp).eq_nil
@[simp] theorem toSorted_singleton {α} (a : α) (cmp : α → α → Int) : toSorted [a] cmp = [a] :=
  List.perm_singleton.mp (toSorted_perm [a] cmp)

theorem toSorted_of_consistent {α} {xs : List α} {cmp : α → α → Int} (h : Consistent cmp xs) :
    toSorted xs cmp = xs.mergeSort (fun a b => decide (cmp a b ≤ 0)) := by
  simp [toSorted, h]

/-- The usual "compare by key" comparators are consistent. -/
theorem consistent_sub {α} (f : α → Int) (xs : List α) : Consistent (fun a b => f a - f b) xs := by
  intro a _ b _ c _; simp only; omega
theorem consistent_sub_rev {α} (f : α → Int) (xs : List α) : Consistent (fun a b => f b - f a) xs := by
  intro a _ b _ c _; simp only; omega

/-- On the elements of `xs` a consistent comparator is a total preorder. -/
theorem Consistent.total_preorder {α} {xs : List α} {cmp : α → α → Int} (h : Consistent cmp xs) :
    (∀ a ∈ xs, ∀ b ∈ xs, ∀ c ∈ xs, cmp a b ≤ 0 → cmp b c ≤ 0 → cmp a c ≤ 0) ∧
    (∀ a ∈ xs, ∀ b ∈ xs, cmp a b ≤ 0 ∨ cmp b a ≤ 0) := by
  have anti : ∀ a ∈ xs, ∀ b ∈ xs, cmp a b < 0 → 0 < cmp b a := by
    intro a ha b hb hab
    rcases Int.lt_trichotomy (cmp b a) 0 with hba | hba | hba
    · have := (h a ha b hb a ha).2.2.2.1 hab hba; have := (h a ha a ha a ha).1; omega
    · have := (h b hb a ha b hb).2.1 hba; omega
    · exact hba
  have anti' : ∀ a ∈ xs, ∀ b ∈ xs, 0 < cmp a b → cmp b a < 0 := by
    intro a ha b hb hab
    rcases Int.lt_trichotomy (cmp b a) 0 with hba | hba | hba
    · exact hba
    · have := (h b hb a ha b hb).2.1 hba; omega
    · have := (h a ha b hb a ha).2.2.2.2 hab hba; have := (h a ha a ha a ha).1; omega
  refine ⟨?_, ?_⟩
  · intro a ha b hb c hc hab hbc
    rcases Int.lt_trichotomy (cmp a c) 0 with hac | hac | hac
    · omega
    · omega
    · exfalso
      have hca := anti' a ha c hc hac
      rcases Int.lt_trichotomy (cmp a b) 0 with hab' | hab' | hab'
      · have hcb := (h c hc a ha b hb).2.2.2.1 hca hab'
        have := anti c hc b hb hcb; omega
      · rcases Int.lt_trichotomy (cmp b c) 0 with hbc' | hbc' | hbc'
        · have := (h a ha b hb a ha).2.1 hab'
          have := (h b hb c hc a ha).2.2.2.1 hbc' hca
          omega
        · have := (h a ha b hb c hc).2.2.1 hab' hbc'; omega
        · omega
      · omega
  · intro a ha b hb
    rcases Int.lt_trichotomy (cmp a b) 0 with hab | hab | hab
    · left; omega
    · left; omega
    · right; have := anti' a ha b hb hab; omega

private theorem mergeSort_attach {α} (xs : List α) (cmp : α → α → Int) :
    xs.mergeSort (fun a b => decide (cmp a b ≤ 0)) =
      (xs.attach.mergeSort (fun a b => decide (cmp a.1 b.1 ≤ 0))).map Subtype.val := by
  rw [List.map_mergeSort (s := fun a b => decide (cmp a b ≤ 0)) (by intros; rfl)]
  simp

/-- Sorted: for a consistent comparator, no element is `cmp`-greater than a later one. -/
theorem pairwise_toSorted {α} {xs : List α} {cmp : α → α → Int} (h : Consistent cmp xs) :
    (toSorted xs cmp).Pairwise (fun a b => cmp a b ≤ 0) := by
  obtain ⟨trans, total⟩ := h.total_preorder
  rw [toSorted_of_consistent h, mergeSort_attach, List.pairwise_map]
  have := List.pairwise_mergeSort (le := fun (a b : {a // a ∈ xs}) => decide (cmp a.1 b.1 ≤ 0))
    (fun a b c hab hbc => by simp at *; exact trans a.1 a.2 b.1 b.2 c.1 c.2 hab hbc)
    (fun a b => by simp; exact total a.1 a.2 b.1 b.2) xs.attach
  exact this.imp (fun h => by simpa using h)

/-- Stable: for a consistent comparator, of two elements in order with `cmp(a, b) ≤ 0`
the first stays first. -/
theorem pair_sublist_toSorted {α} {xs : List α} {cmp : α → α → Int} (h : Consistent cmp xs)
    {a b : α} (hab : cmp a b ≤ 0) (hs : [a, b].Sublist xs) : [a, b].Sublist (toSorted xs cmp) := by
  obtain ⟨trans, total⟩ := h.total_preorder
  rw [toSorted_of_consistent h, mergeSort_attach]
  rw [← List.attach_map_subtype_val xs, List.sublist_map_iff] at hs
  obtain ⟨l', hl', heq⟩ := hs
  match l', heq with
  | [a', b'], heq =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := List.pair_sublist_mergeSort (le := fun (a b : {a // a ∈ xs}) => decide (cmp a.1 b.1 ≤ 0))
      (fun a b c hab hbc => by simp at *; exact trans a.1 a.2 b.1 b.2 c.1 c.2 hab hbc)
      (fun a b => by simp; exact total a.1 a.2 b.1 b.2) (by simpa using hab) hl'
    simpa using this.map Subtype.val

/-- An already sorted list is unchanged by a consistent comparator. -/
theorem toSorted_of_pairwise {α} {xs : List α} {cmp : α → α → Int} (h : Consistent cmp xs)
    (hs : xs.Pairwise (fun a b => cmp a b ≤ 0)) : toSorted xs cmp = xs := by
  rw [toSorted_of_consistent h]
  exact List.mergeSort_of_pairwise (hs.imp (fun h => by simpa using h))

end VReact.JS
