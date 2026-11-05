import VReact.Attr
import VReact.Core
/-!
# List facts for automation

React state is mostly immutable lists updated by `filter` (remove), `map`
(update) and append (insert); keyed lists require distinct keys.  These lemmas
let `grind` move key-uniqueness and membership facts through those operations.
-/
namespace VReact

/-- Removing elements keeps keys distinct. -/
theorem nodup_map_filter {α β} (f : α → β) (p : α → Bool) (l : List α) (h : (l.map f).Nodup) :
    ((l.filter p).map f).Nodup :=
  h.sublist ((List.filter_sublist).map f)
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

@[vreact_simp] theorem nodup_reverse_iff {α} (xs : List α) : xs.reverse.Nodup ↔ xs.Nodup := by
  simp only [List.Nodup, List.pairwise_reverse]
  exact ⟨fun h => h.imp (fun h e => h e.symm), fun h => h.imp (fun h e => h e.symm)⟩

end VReact
