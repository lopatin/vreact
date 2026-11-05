import VReact.Attr
import VReact.Core
/-!
# List facts for automation

React state is mostly immutable lists updated by `filter` (remove), `map`
(update) and append (insert); keyed lists require distinct keys.  These lemmas
let `grind` move key-uniqueness and membership facts through those operations,
through the views rendered from them (`slice`, `toSorted`, `toReversed`, `range`),
and relate counts `(xs.filter p).length` before and after an update.
-/
namespace VReact

/-! ## Sub-permutations: distinct keys through chains of list operations

The views rendered from state are chains of list operations (`items.toSorted(cmp).slice(a, b)`,
`xs.filter(p).slice(2).toReversed()`, …).  Each operation that neither duplicates nor invents
elements is a sub-permutation of its input (`SubPerm (op l) l`: a permutation of a sublist), the
relation is transitive, and transfer lemmas move `Nodup` facts (distinct keys) and counts from
`l₂` to `l₁`.  `vreact_subperm` (`Tactic.lean`) composes the steps of a chain down to a list with
a known `Nodup` (or count), and adds the transferred fact.  (As `grind` patterns, the steps were
instantiated for every list operation of a goal, and the transfers reached `Nodup`s of large
literal lists: too costly.)  The one-step patterns below cover a single operation whose input
fact is in the E-graph. -/

/-- `l₁` is a permutation of a sublist of `l₂` (Mathlib's `List.Subperm`). -/
def SubPerm {α} (l₁ l₂ : List α) : Prop := ∃ l : List α, l.Perm l₁ ∧ l.Sublist l₂

theorem SubPerm.of_sublist {α} {l₁ l₂ : List α} (h : l₁.Sublist l₂) : SubPerm l₁ l₂ := ⟨l₁, .refl _, h⟩
theorem SubPerm.of_perm {α} {l₁ l₂ : List α} (h : l₁.Perm l₂) : SubPerm l₁ l₂ := ⟨l₂, h.symm, .refl _⟩
theorem SubPerm.map {α β} (f : α → β) {l₁ l₂ : List α} (h : SubPerm l₁ l₂) : SubPerm (l₁.map f) (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h; exact ⟨l.map f, hp.map f, hs.map f⟩
theorem SubPerm.nodup {α} {l₁ l₂ : List α} (h : SubPerm l₁ l₂) (h₂ : l₂.Nodup) : l₁.Nodup := by
  obtain ⟨l, hp, hs⟩ := h; exact hp.nodup_iff.mp (h₂.sublist hs)
theorem SubPerm.nodup_map {α β} {f : α → β} {l₁ l₂ : List α} (h : SubPerm l₁ l₂) (h₂ : (l₂.map f).Nodup) :
    (l₁.map f).Nodup := (h.map f).nodup h₂
theorem SubPerm.length_filter_le {α} (p : α → Bool) {l₁ l₂ : List α} (h : SubPerm l₁ l₂) :
    (l₁.filter p).length ≤ (l₂.filter p).length := by
  obtain ⟨l, hp, hs⟩ := h; exact (hp.filter p).length_eq ▸ (hs.filter p).length_le

-- the operations
theorem subPerm_filter {α} (p : α → Bool) (l : List α) : SubPerm (l.filter p) l := .of_sublist List.filter_sublist
theorem subPerm_slice {α} (l : List α) (a : Int) (b : Option Int) : SubPerm (JS.slice l a b) l :=
  .of_sublist (JS.slice_sublist l a b)
theorem subPerm_toSorted {α} (l : List α) (cmp : α → α → Int) : SubPerm (JS.toSorted l cmp) l :=
  .of_perm (JS.toSorted_perm l cmp)
theorem subPerm_reverse {α} (l : List α) : SubPerm l.reverse l := .of_perm (List.reverse_perm l)
theorem subPerm_take {α} (n : Nat) (l : List α) : SubPerm (l.take n) l := .of_sublist (List.take_sublist n l)
theorem subPerm_drop {α} (n : Nat) (l : List α) : SubPerm (l.drop n) l := .of_sublist (List.drop_sublist n l)
theorem SubPerm.trans {α} {l₁ l₂ l₃ : List α} (h₁ : SubPerm l₁ l₂) (h₂ : SubPerm l₂ l₃) : SubPerm l₁ l₃ := by
  obtain ⟨l, hp, hs⟩ := h₁
  obtain ⟨l', hp', hs'⟩ := h₂
  obtain ⟨l'', hp'', hs''⟩ := List.exists_perm_sublist hs hp'.symm
  exact ⟨l'', hp''.trans hp, hs''.trans hs'⟩
theorem SubPerm.length_le {α} {l₁ l₂ : List α} (h : SubPerm l₁ l₂) : l₁.length ≤ l₂.length := by
  obtain ⟨l, hp, hs⟩ := h; exact hp.length_eq ▸ hs.length_le

/-- Removing elements keeps keys distinct. -/
theorem nodup_map_filter {α β} (f : α → β) (p : α → Bool) (l : List α) (h : (l.map f).Nodup) :
    ((l.filter p).map f).Nodup :=
  (subPerm_filter p l).nodup_map h
grind_pattern nodup_map_filter => (l.filter p).map f, (l.map f).Nodup

attribute [grind →] List.mem_of_find?_eq_some
-- `xs[i]` is an element of `xs` (`JS.get_mem`, after `JS.get` is unfolded to `getElem`)
grind_pattern List.getElem_mem => l[n]'h
attribute [grind =] List.all_eq_true List.any_eq_true

-- membership and distinctness distribute over the list operations
attribute [vreact_simp] List.nodup_append List.map_append List.mem_append List.mem_map List.mem_filter
  List.nodup_cons List.mem_singleton List.nodup_nil List.filter_append List.append_assoc

/-! Keys of `range(n)` and of lists of ints/strings used directly as keys
(`List.map Key.int xs` is the eta-reduced form `nodup_map_key_int` does not match). -/
@[vreact_simp] theorem nodup_map_key_int' (xs : List Int) : (xs.map Key.int).Nodup ↔ xs.Nodup := by
  simpa using nodup_map_key_int xs id
@[vreact_simp] theorem nodup_map_key_str' (xs : List JS.Str) : (xs.map Key.str).Nodup ↔ xs.Nodup := by
  simpa using nodup_map_key_str xs id

/-! The other list methods: `toSorted` is a permutation, `slice` a sublist, `toReversed` a
reversal, `with` a pointwise update, `flatMap` a concatenation (the facts are in `JS.lean`). -/
attribute [vreact_simp] JS.length_toSorted JS.mem_toSorted JS.nodup_map_toSorted JS.nodup_toSorted
  JS.length_filter_toSorted JS.toSorted_nil JS.toSorted_singleton JS.nodup_range
  JS.withAt_eq_set List.length_set List.mem_reverse List.length_reverse List.map_reverse
  List.mem_flatMap
  JS.nodup_map_set_swap JS.nodup_set_swap JS.mem_set_swap JS.length_filter_set_swap

/-! Counts (`xs.filter(p).length`) under the usual state updates: append is handled by
`filter_append`; an update `map f` is pushed under the filter (`filter_map`), so marking
all done gives a constant predicate; a deletion `filter q` can only lower a count; and a
count can only grow when its predicate gets weaker. -/
@[vreact_simp] theorem filter_const_true {α} (l : List α) : l.filter (fun _ => true) = l := by
  simp
@[vreact_simp] theorem filter_const_false {α} (l : List α) : l.filter (fun _ => false) = [] := by
  simp
attribute [vreact_simp] List.filter_map List.length_map List.length_filter_le

theorem length_filter_filter_le {α} (p q : α → Bool) (l : List α) :
    ((l.filter q).filter p).length ≤ (l.filter p).length :=
  ((List.filter_sublist).filter p).length_le
grind_pattern length_filter_filter_le => (l.filter q).filter p

theorem length_filter_le_of_imp {α} {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, q x = true → p x = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  simpa [List.countP_eq_length_filter] using List.countP_mono_left h
grind_pattern length_filter_le_of_imp => (l.filter q).length, (l.filter p).length

theorem length_filter_add_length_filter_not {α} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [List.filter_cons, h] <;> omega
grind_pattern length_filter_add_length_filter_not => (l.filter p).length, (l.filter (fun a => !p a)).length

/-- Deleting by a key of a list with distinct keys removes at most one element. -/
theorem length_le_length_filter_add_one {α β} {f : α → β} {p : α → Bool} {l : List α}
    (h : (l.map f).Nodup) (hp : ∀ x ∈ l, ∀ y ∈ l, p x = false → p y = false → f x = f y) :
    l.length ≤ (l.filter p).length + 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    have ih' := ih h.2 (fun x hx y hy => hp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    cases ha : p a
    · have : t.filter p = t := by
        rw [List.filter_eq_self]
        intro y hy
        cases hpy : p y
        · exact absurd (hp y (List.mem_cons_of_mem _ hy) a List.mem_cons_self hpy ha) (h.1 y hy)
        · rfl
      simp [List.filter_cons, ha, this]
    · simp [List.filter_cons, ha]; omega
grind_pattern length_le_length_filter_add_one => (l.map f).Nodup, l.filter p
-- … and removes at least one element when one matches
theorem length_filter_lt_of_mem {α} {p : α → Bool} {l : List α} {x : α} (hx : x ∈ l) (hp : p x = false) :
    (l.filter p).length < l.length :=
  List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp [hp]⟩
grind_pattern length_filter_lt_of_mem => x ∈ l, l.filter p

/-! ### Counts by key

`grind` cannot match a pattern inside a predicate (`fun y => !JS.eq y.id k`), so the facts
below are added by `vreact_keyfacts` (`Tactic.lean`) for each count `(l.filter P).length` of a
goal whose predicate has the shape they describe.  Together with
`Nodup ↔ ∀ a, count a ≤ 1` and `0 < count a ↔ a ∈ ·` they give: deleting by the key of a
present element of a list with distinct keys removes exactly one element; a map-update by key
changes a count by at most one, and by exactly the change at that element when it is
present. -/

/-- Filtering out key `k` removes as many elements as `k` occurs among the keys. -/
theorem length_filter_ne_key {α β} [DecidableEq β] (f : α → β) (k : β) (l : List α) :
    (l.filter (fun y => !JS.eq (f y) k)).length + (l.map f).count k = l.length := by
  induction l with
  | nil => simp
  | cons a t ih => by_cases h : f a = k <;> simp [h, JS.eq] at * <;> omega
theorem length_filter_ne_key' {α β} [DecidableEq β] (f : α → β) (k : β) (l : List α) :
    (l.filter (fun y => !JS.eq k (f y))).length + (l.map f).count k = l.length := by
  induction l with
  | nil => simp
  | cons a t ih => by_cases h : f a = k <;> simp [h, JS.eq, eq_comm (a := k)] at * <;> omega
/-- Keeping key `k` keeps as many elements as `k` occurs among the keys. -/
theorem length_filter_eq_key {α β} [DecidableEq β] (f : α → β) (k : β) (l : List α) :
    (l.filter (fun y => JS.eq (f y) k)).length = (l.map f).count k := by
  have := length_filter_ne_key f k l
  have := length_filter_add_length_filter_not (fun y => JS.eq (f y) k) l
  omega
theorem length_filter_eq_key' {α β} [DecidableEq β] (f : α → β) (k : β) (l : List α) :
    (l.filter (fun y => JS.eq k (f y))).length = (l.map f).count k := by
  have := length_filter_ne_key' f k l
  have := length_filter_add_length_filter_not (fun y => JS.eq k (f y)) l
  omega

/-- Two predicates that agree on the elements whose key is not `k` (a count before and after
the map-update `xs.map(x => x.id === k ? {...x, done: !x.done} : x)`): their counts differ by at
most the number of elements with key `k`. -/
theorem length_filter_le_of_agree_off_key {α β} [DecidableEq β] {p q : α → Bool} (f : α → β) (k : β)
    (l : List α) (h : ∀ x, f x ≠ k → p x = q x) :
    (l.filter p).length ≤ (l.filter q).length + (l.map f).count k := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases hk : f a = k
    · have e : ((a :: t).map f).count k = (t.map f).count k + 1 := by simp [List.count_cons, hk]
      rw [e]
      cases hpa : p a <;> cases hqa : q a <;>
        simp only [List.filter_cons, hpa, hqa, if_true, if_false, Bool.false_eq_true, List.length_cons] <;> omega
    · simp only [List.filter_cons, h a hk, List.map_cons, List.count_cons, hk, beq_iff_eq]
      cases q a <;> simp <;> omega
/-- … and with distinct keys and `x₀` the element with key `k`, they differ exactly by the
difference at `x₀`. -/
theorem length_filter_agree_off_key {α β} [DecidableEq β] {p q : α → Bool} (f : α → β) (k : β)
    (l : List α) (h : ∀ x, f x ≠ k → p x = q x) :
    ∀ x₀ ∈ l, f x₀ = k → (l.map f).Nodup →
      (l.filter p).length + (if q x₀ = true then 1 else 0) = (l.filter q).length + (if p x₀ = true then 1 else 0) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    intro x₀ hx hk hn
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hpq : t.filter p = t.filter q := List.filter_congr fun y hy => h y (fun e => hn.1 y hy (e.trans hk.symm))
      cases hp : p x₀ <;> cases hq : q x₀ <;> simp [List.filter_cons, hp, hq, hpq]
    · have hka : f a ≠ k := fun e => hn.1 x₀ hx' (hk.trans e.symm)
      have := ih x₀ hx' hk hn.2
      simp only [List.filter_cons, h a hka]
      cases q a <;> simp <;> omega

@[vreact_simp] theorem nodup_reverse_iff {α} (xs : List α) : xs.reverse.Nodup ↔ xs.Nodup := by
  simp only [List.Nodup, List.pairwise_reverse]
  exact ⟨fun h => h.imp (fun h e => h e.symm), fun h => h.imp (fun h e => h e.symm)⟩

end VReact
