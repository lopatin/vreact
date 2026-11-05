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

/-! ### `slice` is a sublist: membership and distinct keys carry over -/

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
