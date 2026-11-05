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

/-- JS number formatting (shortest round-trip) is not modelled: opaque. -/
opaque numToString : Float → Str
instance : ToJS Float := ⟨numToString⟩

def str {α} [ToJS α] (a : α) : Str := ToJS.str a

/-! ## Integers (the `int` type of VTS) -/

/-- `a % b` on integers (ECMA-262 Number::remainder): the result has the sign of
the dividend and magnitude `|a| mod |b|`.  (`%` below is Lean's Euclidean `emod`.) -/
def rem (a b : Int) (_h : b ≠ 0) : Int :=
  if 0 ≤ a then a % (b.natAbs : Int) else -((-a) % (b.natAbs : Int))
/-- `Math.floor(a / b)` on integers. (Lean's `/` on `Int` rounds toward −∞ for positive divisors.) -/
def floorDiv (a b : Int) (_h : b ≠ 0) : Int := if 0 < b then a / b else (-a) / (-b)
/-- `Math.trunc(a / b)` on integers. -/
def truncDiv (a b : Int) (_h : b ≠ 0) : Int :=
  if (0 ≤ a) = (0 < b) then ((a.natAbs / b.natAbs : Nat) : Int) else -((a.natAbs / b.natAbs : Nat) : Int)
/-- `Math.abs` -/
def abs (a : Int) : Int := if a < 0 then -a else a
/-- `Math.sign` -/
def sign (a : Int) : Int := if a < 0 then -1 else if a = 0 then 0 else 1

/-! ## Floats (the `number` type of VTS): IEEE-754 doubles, executable but proof-opaque. -/

/-- `Math.round` rounds half-way cases towards +∞. -/
def mathRound (x : Float) : Float := Float.floor (x + 0.5)

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

/-- `xs.with(i, v)` (ES2023): throws RangeError when out of range, hence the obligation. -/
def withAt {α} (xs : List α) (i : Int) (v : α) (_h : 0 ≤ i ∧ i < xs.length) : List α :=
  xs.set i.toNat v

/-- `xs.toSorted(cmp)`: a stable sort; `a` stays before `b` when `cmp(a, b) ≤ 0`. -/
def toSorted {α} (xs : List α) (cmp : α → α → Int) : List α :=
  xs.mergeSort (fun a b => decide (cmp a b ≤ 0))

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

end VReact.JS
