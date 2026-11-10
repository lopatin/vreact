import VReact.JS
import VReact.Attr
import VReact.Lists
/-!
# VReact.JS.JSMap / JSSet — JavaScript `Map` and `Set` with primitive keys

A JS `Map` (`Set`) with keys (elements) compared by SameValueZero is modelled as the list of its
entries (elements) **in insertion order**, with pairwise distinct keys.  VTS admits only keys whose
SameValueZero is Lean equality: `boolean`, `int`, `string` and string-literal enums (never
`number`: NaN, ±0; never objects: identity; never optional types: `null` and `undefined` are
different keys), and in a generic function a type parameter with an equality constraint
(`K extends int | string`): its body is proved for every `K` with `[DecidableEq K]`, and it is
instantiated only with those types.  The operations follow ECMA-262 exactly, including the
observable order:

* `m.set(k, v)` on a present key replaces the value **in place** (the key keeps its position);
  on a new key it appends the entry;
* `m.delete(k)` removes the entry (a later `set` of `k` appends it again, at the end);
* `new Map(entries)` is `set` of each entry in turn, so a duplicate key keeps its *first*
  position and takes its *last* value; `new Set(xs)` keeps first occurrences;
* `size` is the number of entries; `keys()`, `values()`, `entries()` (and `for…of`, spread) list
  them in insertion order.

The translator allows `set`/`add`/`delete`/`clear` only on a fresh, unaliased copy (a pure chain
`new Map(m).set(k, v)`, or statements on a local `const n = new Map(m)` that nothing else can
observe), so the pure functions here are exact.  `===` on maps (identity) is rejected by the
translator; Lean `=` on `JSMap` is equality of the entry lists (order included), i.e.
observational equality.

The automation (`vreact_auto`) sees `get`, `keys`, `values` and `size` as atoms with algebraic
`set`/`delete` lemmas (`vreact_simp` + `grind`); a Set is list-transparent (`elems_add`,
`elems_delete`, `size_eq` rewrite it into list operations).  The distinct-keys facts are also
stated as `.post` contracts of `keys`/`entries`/`elems`, so that `vreact_contracts` adds them as
hypotheses (`vreact_subperm` moves `Nodup` facts only from hypotheses).
-/
namespace VReact.JS

/-- Lookup of a key in an association list (first occurrence). -/
def lookup {K V : Type} [DecidableEq K] (k : K) : List (K × V) → Option V
  | [] => none
  | p :: rest => if p.1 = k then some p.2 else lookup k rest

section Lookup
variable {K V : Type} [DecidableEq K]

theorem lookup_eq_none {k : K} {l : List (K × V)} : lookup k l = none ↔ k ∉ l.map Prod.fst := by
  induction l with
  | nil => simp [lookup]
  | cons p rest ih => by_cases h : p.1 = k <;> simp [lookup, h, ih] <;> grind

theorem mem_of_lookup {k : K} {v : V} {l : List (K × V)} (h : lookup k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [lookup] at h
  | cons p rest ih =>
    by_cases hp : p.1 = k
    · simp [lookup, hp] at h; subst h; obtain ⟨a, b⟩ := p; simp_all
    · simp [lookup, hp] at h; exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {k : K} {v : V} {l : List (K × V)} (hn : (l.map Prod.fst).Nodup) (h : (k, v) ∈ l) :
    lookup k l = some v := by
  induction l with
  | nil => simp at h
  | cons p rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with rfl | h'
    · simp [lookup]
    · have : p.1 ≠ k := fun e => hn.1 ⟨(k, v), h', e.symm⟩
      simp [lookup, this, ih hn.2 h']

theorem lookup_append (k : K) (l₁ l₂ : List (K × V)) : lookup k (l₁ ++ l₂) = (lookup k l₁).or (lookup k l₂) := by
  induction l₁ with
  | nil => simp [lookup]
  | cons p rest ih => by_cases hp : p.1 = k <;> simp [lookup, hp, ih]

theorem lookup_update (k k' : K) (v : V) (l : List (K × V)) :
    lookup k' (l.map (fun p => if p.1 = k then (k, v) else p)) =
      if k' = k then (if k ∈ l.map Prod.fst then some v else none) else lookup k' l := by
  induction l with
  | nil => simp [lookup]
  | cons p rest ih =>
    by_cases hp : p.1 = k <;> by_cases hk : k' = k <;> simp_all [lookup] <;> grind

theorem lookup_filter_ne (k k' : K) (l : List (K × V)) :
    lookup k' (l.filter (fun p => !JS.eq p.1 k)) = if k' = k then none else lookup k' l := by
  induction l with
  | nil => simp [lookup]
  | cons p rest ih =>
    by_cases hp : p.1 = k <;> by_cases hk : k' = k <;> simp_all [lookup, JS.eq] <;> grind
end Lookup

/-- A JS `Map` with primitive keys: its entries in insertion order, keys pairwise distinct. -/
structure JSMap (K V : Type) where
  entries : List (K × V)
  nodup : (entries.map Prod.fst).Nodup

namespace JSMap
variable {K V : Type}

/-- `[...m.keys()]` -/
def keys (m : JSMap K V) : List K := m.entries.map Prod.fst
/-- `[...m.values()]` -/
def values (m : JSMap K V) : List V := m.entries.map Prod.snd
/-- `m.size` -/
def size (m : JSMap K V) : Int := m.entries.length
/-- `new Map()`, and `m.clear()` (on a fresh local). -/
def empty : JSMap K V := ⟨[], List.nodup_nil⟩

instance : Inhabited (JSMap K V) := ⟨empty⟩
theorem ext_entries {a b : JSMap K V} (h : a.entries = b.entries) : a = b := by cases a; cases b; simp_all
instance [DecidableEq K] [DecidableEq V] : DecidableEq (JSMap K V) := fun a b =>
  if h : a.entries = b.entries then isTrue (ext_entries h) else isFalse (fun e => h (e ▸ rfl))
instance [Repr K] [Repr V] : Repr (JSMap K V) := ⟨fun m _ => "new Map(" ++ reprArg m.entries ++ ")"⟩

theorem keys_nodup (m : JSMap K V) : m.keys.Nodup := m.nodup

variable [DecidableEq K]

/-- `m.get(k)` (`undefined` for a missing key: VTS map values are never optional). -/
def get (m : JSMap K V) (k : K) : Option V := lookup k m.entries
/-- `m.has(k)` -/
def has (m : JSMap K V) (k : K) : Bool := decide (k ∈ m.keys)

private theorem nodup_update (m : JSMap K V) (k : K) (v : V) :
    ((m.entries.map (fun p => if p.1 = k then (k, v) else p)).map Prod.fst).Nodup := by
  have : (m.entries.map (fun p => if p.1 = k then (k, v) else p)).map Prod.fst = m.entries.map Prod.fst := by
    rw [List.map_map]; apply List.map_congr_left; intro p _; by_cases hp : p.1 = k <;> simp [hp]
  rw [this]; exact m.nodup
omit [DecidableEq K] in
private theorem nodup_push (m : JSMap K V) (k : K) (v : V) (h : k ∉ m.keys) :
    ((m.entries ++ [(k, v)]).map Prod.fst).Nodup := by
  have hn := m.nodup
  simp only [keys] at h
  rw [List.map_append, List.nodup_append]
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact h ha

/-- `m.set(k, v)` (on a fresh copy, `new Map(m).set(k, v)`): a present key keeps its position
and gets the new value; a new key is appended (insertion order). -/
def set (m : JSMap K V) (k : K) (v : V) : JSMap K V :=
  if h : k ∈ m.keys then ⟨m.entries.map (fun p => if p.1 = k then (k, v) else p), nodup_update m k v⟩
  else ⟨m.entries ++ [(k, v)], nodup_push m k v h⟩

/-- `m.delete(k)` as a statement on a fresh local (the entry is removed; its Bool result is not
modelled: VTS accepts `delete` only as a statement).  The filter has the shape the translator emits
for `xs.filter((x) => x.id !== k)`, so the count-by-key facts of `Lists.lean` apply to it. -/
def delete (m : JSMap K V) (k : K) : JSMap K V :=
  ⟨m.entries.filter (fun p => !JS.eq p.1 k), m.nodup.sublist (List.filter_sublist.map _)⟩

/-- `set` of each entry in turn. -/
def setAll (m : JSMap K V) : List (K × V) → JSMap K V
  | [] => m
  | p :: rest => setAll (m.set p.1 p.2) rest
/-- `new Map(entries)`: a duplicate key keeps its first position and takes its last value. -/
def ofList (xs : List (K × V)) : JSMap K V := setAll empty xs

/-! ### the lemma set -/

theorem entries_set (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).entries = if k ∈ m.keys then m.entries.map (fun p => if p.1 = k then (k, v) else p)
      else m.entries ++ [(k, v)] := by
  unfold set; split <;> simp_all

theorem get_set (m : JSMap K V) (k k' : K) (v : V) :
    (m.set k v).get k' = if k' = k then some v else m.get k' := by
  unfold get; rw [entries_set]
  split
  · rename_i hk; rw [lookup_update]; simp only [keys] at hk; simp [hk]
  · rename_i hk; rw [lookup_append]
    by_cases h : k' = k
    · subst h; simp only [keys] at hk; simp [lookup_eq_none.mpr hk, lookup]
    · simp [h, lookup]; cases lookup k' m.entries <;> simp [Ne.symm h]

theorem get_delete (m : JSMap K V) (k k' : K) :
    (m.delete k).get k' = if k' = k then none else m.get k' := lookup_filter_ne k k' m.entries

theorem get_empty (k : K) : (empty : JSMap K V).get k = none := rfl

theorem get_eq_none_iff (m : JSMap K V) (k : K) : m.get k = none ↔ k ∉ m.keys := lookup_eq_none
theorem get_eq_some_iff (m : JSMap K V) (k : K) (v : V) : m.get k = some v ↔ (k, v) ∈ m.entries :=
  ⟨mem_of_lookup, lookup_of_mem m.nodup⟩

theorem has_def (m : JSMap K V) (k : K) : m.has k = decide (k ∈ m.keys) := rfl
theorem get_of_mem_entries {m : JSMap K V} {k : K} {v : V} (h : (k, v) ∈ m.entries) : m.get k = some v :=
  (get_eq_some_iff m k v).mpr h
theorem has_eq_true_iff (m : JSMap K V) (k : K) : m.has k = true ↔ k ∈ m.keys := by simp [has]
theorem has_eq_false_iff (m : JSMap K V) (k : K) : m.has k = false ↔ k ∉ m.keys := by simp [has]

theorem keys_set (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).keys = if k ∈ m.keys then m.keys else m.keys ++ [k] := by
  unfold keys; rw [entries_set]
  by_cases hk : k ∈ m.entries.map Prod.fst
  · simp only [keys, hk, ite_true]
    rw [List.map_map]; apply List.map_congr_left; intro p _; by_cases hp : p.1 = k <;> simp [hp]
  · simp [keys, hk]

theorem keys_set_of_mem (m : JSMap K V) (k : K) (v : V) (h : k ∈ m.keys) : (m.set k v).keys = m.keys := by
  rw [keys_set]; simp [h]
theorem keys_set_of_not_mem (m : JSMap K V) (k : K) (v : V) (h : k ∉ m.keys) : (m.set k v).keys = m.keys ++ [k] := by
  rw [keys_set]; simp [h]
theorem mem_keys_set (m : JSMap K V) (k k' : K) (v : V) : k' ∈ (m.set k v).keys ↔ k' = k ∨ k' ∈ m.keys := by
  rw [keys_set]; by_cases hk : k ∈ m.keys <;> simp [hk] <;> grind

theorem mem_keys_delete (m : JSMap K V) (k k' : K) : k' ∈ (m.delete k).keys ↔ ¬ k' = k ∧ k' ∈ m.keys := by
  unfold keys delete; simp [JS.eq]; grind

theorem keys_delete (m : JSMap K V) (k : K) : (m.delete k).keys = m.keys.filter (fun x => !JS.eq x k) := by
  unfold keys delete; simp [List.filter_map, Function.comp_def]

omit [DecidableEq K] in
theorem size_eq_length_keys (m : JSMap K V) : m.size = (m.keys.length : Int) := by simp [size, keys]

theorem size_set (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).size = if k ∈ m.keys then m.size else m.size + 1 := by
  rw [size_eq_length_keys, size_eq_length_keys, keys_set]; split <;> simp

theorem size_delete (m : JSMap K V) (k : K) :
    (m.delete k).size = if k ∈ m.keys then m.size - 1 else m.size := by
  rw [size_eq_length_keys, size_eq_length_keys, keys_delete]
  have h := VReact.length_filter_ne_key (fun x : K => x) k m.keys
  simp only [List.map_id'] at h
  have hc := List.nodup_iff_count.mp (keys_nodup m) k
  split
  · rename_i hk; have := List.count_pos_iff.mpr hk; omega
  · rename_i hk; have := List.count_eq_zero.mpr hk; omega

theorem length_keys_set (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).keys.length = if k ∈ m.keys then m.keys.length else m.keys.length + 1 := by
  rw [keys_set]; split <;> simp
theorem length_keys_delete (m : JSMap K V) (k : K) :
    (m.delete k).keys.length = if k ∈ m.keys then m.keys.length - 1 else m.keys.length := by
  rw [keys_delete]
  have h := VReact.length_filter_ne_key (fun x : K => x) k m.keys
  simp only [List.map_id'] at h
  have hc := List.nodup_iff_count.mp (keys_nodup m) k
  split
  · rename_i hk; have := List.count_pos_iff.mpr hk; omega
  · rename_i hk; have := List.count_eq_zero.mpr hk; omega
theorem mem_values_set (m : JSMap K V) (k : K) (v x : V) :
    x ∈ (m.set k v).values ↔ x = v ∨ x ∈ (m.delete k).values := by
  unfold values delete; rw [entries_set]; split
  · rename_i hk; simp only [keys, List.mem_map] at hk; obtain ⟨p0, hp0, rfl⟩ := hk
    simp [List.mem_map, List.mem_filter, JS.eq]
    constructor
    · rintro ⟨a, b, hab, e⟩; by_cases h : a = p0.1 <;> simp_all; right; exact ⟨a, hab, h⟩
    · rintro (rfl | ⟨a, hab, hne⟩)
      · exact ⟨p0.1, p0.2, hp0, by simp⟩
      · exact ⟨a, x, hab, by simp [hne]⟩
  · rename_i hk; simp only [keys, List.mem_map, not_exists, not_and] at hk
    simp [List.mem_map, List.mem_filter, JS.eq]
    constructor
    · rintro (⟨a, h⟩ | rfl)
      · right; exact ⟨a, h, fun e => hk _ h (by simp [e])⟩
      · left; rfl
    · rintro (rfl | ⟨a, h, _⟩)
      · exact Or.inr rfl
      · exact Or.inl ⟨a, h⟩

theorem mem_values_of_mem_delete {m : JSMap K V} {k : K} {x : V} (h : x ∈ (m.delete k).values) : x ∈ m.values := by
  unfold values delete at h; unfold values
  exact (List.filter_sublist.map Prod.snd).subset h

theorem mem_values_of_get {m : JSMap K V} {k : K} {v : V} (h : m.get k = some v) : v ∈ m.values :=
  List.mem_map.mpr ⟨(k, v), (get_eq_some_iff m k v).mp h, rfl⟩

theorem setAll_nil (m : JSMap K V) : m.setAll [] = m := rfl
theorem setAll_cons (m : JSMap K V) (p : K × V) (xs) : m.setAll (p :: xs) = (m.set p.1 p.2).setAll xs := rfl
theorem ofList_eq (xs : List (K × V)) : ofList xs = empty.setAll xs := rfl
omit [DecidableEq K] in
theorem keys_empty : (empty : JSMap K V).keys = [] := rfl
omit [DecidableEq K] in
theorem size_empty : (empty : JSMap K V).size = 0 := rfl
omit [DecidableEq K] in
theorem values_empty : (empty : JSMap K V).values = [] := rfl
omit [DecidableEq K] in
theorem entries_empty : (empty : JSMap K V).entries = [] := rfl

omit [DecidableEq K] in
theorem size_nonneg (m : JSMap K V) : 0 ≤ m.size := by simp [size]
theorem mem_keys_of_get {m : JSMap K V} {k : K} {v : V} (h : m.get k = some v) : k ∈ m.keys :=
  Classical.byContradiction fun hk => by rw [(get_eq_none_iff m k).mpr hk] at h; cases h
theorem mem_keys_setAll (m : JSMap K V) (xs : List (K × V)) (k : K) :
    k ∈ (m.setAll xs).keys ↔ k ∈ m.keys ∨ k ∈ xs.map Prod.fst := by
  induction xs generalizing m with
  | nil => simp [setAll]
  | cons p rest ih => rw [setAll_cons, ih, mem_keys_set]; simp; grind
theorem get_setAll_of_not_mem (m : JSMap K V) (xs : List (K × V)) (k : K) (h : k ∉ xs.map Prod.fst) :
    (m.setAll xs).get k = m.get k := by
  induction xs generalizing m with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [setAll_cons, ih _ h.2, get_set]; simp [h.1]
theorem get_ofList_of_nodup (xs : List (K × V)) (hn : (xs.map Prod.fst).Nodup) (k : K) (v : V) :
    (empty.setAll xs).get k = some v ↔ (k, v) ∈ xs := by
  suffices ∀ (m : JSMap K V), (∀ p ∈ xs, p.1 ∉ m.keys) → ((m.setAll xs).get k = some v ↔ (k, v) ∈ xs ∨ (k ∉ xs.map Prod.fst ∧ m.get k = some v)) by
    rw [this empty (by simp [keys_empty])]; simp [get_empty]
  induction xs with
  | nil => intro m _; simp [setAll]
  | cons p rest ih =>
    intro m hm
    simp only [List.map_cons, List.nodup_cons] at hn
    rw [setAll_cons, ih hn.2 _ (fun q hq => by
      rw [mem_keys_set]; rintro (e | e)
      · exact hn.1 (e ▸ List.mem_map_of_mem hq)
      · exact hm q (List.mem_cons_of_mem _ hq) e)]
    rw [get_set]
    by_cases hk : k = p.1
    · subst hk
      have hn1 : ∀ x, (p.1, x) ∉ rest := fun x hx => hn.1 (List.mem_map.mpr ⟨_, hx, rfl⟩)
      obtain ⟨a, b⟩ := p
      simp only at hn1 ⊢
      simp [hn1]; grind
    · simp [hk]; grind
/-- An index built from a list by a key function (`new Map(xs.map((x) => [x.id, x]))`, or the loop
`for (const x of xs) n.set(x.id, x)` from an empty `n`) with distinct keys maps each element's
key to that element (`distinct(xs, (x) => x.id)` → `r.get(x.id)` is `x`, for every `x` of `xs`). -/
theorem get_ofList_map_of_nodup {α} (xs : List α) (h : α → K × V) (hn : (xs.map (fun y => (h y).1)).Nodup)
    (x : α) (hx : x ∈ xs) : (empty.setAll (xs.map h)).get (h x).1 = some (h x).2 := by
  rw [get_ofList_of_nodup]
  · exact List.mem_map_of_mem hx
  · simpa [List.map_map, Function.comp_def] using hn
theorem entries_delete (m : JSMap K V) (k : K) : (m.delete k).entries = m.entries.filter (fun p => !JS.eq p.1 k) := rfl
omit [DecidableEq K] in
theorem nodup_entries_fst (m : JSMap K V) : (m.entries.map (fun p => p.1)).Nodup := m.nodup

theorem mem_entries_set (m : JSMap K V) (k : K) (v : V) (p : K × V) :
    p ∈ (m.set k v).entries ↔ p = (k, v) ∨ (p ∈ m.entries ∧ ¬ p.1 = k) := by
  rw [entries_set]; split
  · rename_i hk
    simp only [List.mem_map]
    constructor
    · rintro ⟨q, hq, e⟩
      by_cases h : q.1 = k
      · simp [h] at e; exact Or.inl e.symm
      · simp [h] at e; subst e; exact Or.inr ⟨hq, h⟩
    · rintro (rfl | ⟨hp, hne⟩)
      · simp only [keys, List.mem_map] at hk
        obtain ⟨q, hq, e⟩ := hk
        exact ⟨q, hq, by simp [e]⟩
      · exact ⟨p, hp, by simp [hne]⟩
  · rename_i hk
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (hp | rfl)
      · right; refine ⟨hp, fun e => hk ?_⟩
        simp only [keys, List.mem_map]; exact ⟨p, hp, e⟩
      · left; rfl
    · rintro (rfl | ⟨hp, _⟩)
      · right; rfl
      · left; exact hp

/-- `m.get(k)` returns the value of `k`'s entry: `(k, v)` is an entry (so an invariant over the
entries, `[...m.entries()].every(([k, v]) => k === v.id)`, applies to the value read). -/
theorem mem_entries_of_get {m : JSMap K V} {k : K} {v : V} (h : m.get k = some v) : (k, v) ∈ m.entries :=
  (get_eq_some_iff m k v).mp h

theorem delete_empty (k : K) : (empty : JSMap K V).delete k = empty := rfl

omit [DecidableEq K] in
/-- `[...m].length === m.size` -/
theorem length_entries (m : JSMap K V) : (m.entries.length : Int) = m.size := rfl
omit [DecidableEq K] in
/-- `[...m.values()].length === m.size` -/
theorem length_values (m : JSMap K V) : (m.values.length : Int) = m.size := by simp [values, size]

/-- An entry of `new Map(pairs)` (of a `for…of` loop of `set`s) is an entry of the start or one of the pairs. -/
theorem mem_entries_setAll {m : JSMap K V} {xs : List (K × V)} {p : K × V} (h : p ∈ (m.setAll xs).entries) :
    p ∈ m.entries ∨ p ∈ xs := by
  induction xs generalizing m with
  | nil => exact Or.inl h
  | cons q rest ih =>
    rw [setAll_cons] at h
    rcases ih h with h' | h'
    · rw [mem_entries_set] at h'
      rcases h' with rfl | ⟨h', _⟩
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl h'
    · exact Or.inr (List.mem_cons_of_mem _ h')

theorem mem_values_setAll {m : JSMap K V} {xs : List (K × V)} {v : V} (h : v ∈ (m.setAll xs).values) :
    v ∈ m.values ∨ v ∈ xs.map Prod.snd := by
  simp only [values, List.mem_map] at h ⊢
  obtain ⟨p, hp, rfl⟩ := h
  rcases mem_entries_setAll hp with h | h
  · exact Or.inl ⟨p, h, rfl⟩
  · exact Or.inr ⟨p, h, rfl⟩

theorem size_setAll_le (m : JSMap K V) (xs : List (K × V)) : (m.setAll xs).size ≤ m.size + xs.length := by
  induction xs generalizing m with
  | nil => simp [setAll]
  | cons q rest ih =>
    rw [setAll_cons]
    have := ih (m.set q.1 q.2)
    have := size_set m q.1 q.2
    split at this <;> simp at * <;> omega

theorem entries_setAll_of_nodup (m : JSMap K V) (xs : List (K × V))
    (h : ((m.entries ++ xs).map Prod.fst).Nodup) : (m.setAll xs).entries = m.entries ++ xs := by
  induction xs generalizing m with
  | nil => simp [setAll]
  | cons q rest ih =>
    rw [setAll_cons]
    have hq : q.1 ∉ m.keys := by
      simp only [List.map_append, List.map_cons, List.nodup_append, List.nodup_cons] at h
      intro hk; exact h.2.2 _ hk _ (List.mem_cons_self ..) rfl
    have he : (m.set q.1 q.2).entries = m.entries ++ [q] := by
      rw [entries_set]; simp [hq]
    rw [ih, he]; · simp
    rw [he]; simpa using h

/-- `new Map(pairs)` with distinct keys has exactly the pairs as entries, in order. -/
theorem entries_ofList_of_nodup (xs : List (K × V)) (h : (xs.map Prod.fst).Nodup) :
    (empty.setAll xs).entries = xs := by
  rw [entries_setAll_of_nodup] <;> simp_all [entries_empty]

theorem size_ofList_of_nodup (xs : List (K × V)) (h : (xs.map Prod.fst).Nodup) :
    (empty.setAll xs).size = xs.length := by
  rw [← length_entries, entries_ofList_of_nodup xs h]

omit [DecidableEq K] in
/-- A Map keyed by a function of its values (`ReadonlyMap<int, Item>` with `k === it.id` for every
entry) has distinct `f`-images of its values: `[...m.values()].map((it) => <li key={it.id}>…)`. -/
theorem nodup_map_values_of_key (m : JSMap K V) (f : V → K) (h : ∀ p ∈ m.entries, p.1 = f p.2) :
    (m.values.map f).Nodup := by
  have : m.values.map f = m.keys := by
    simp only [values, keys, List.map_map]
    apply List.map_congr_left; intro p hp; simp [h p hp]
  rw [this]; exact m.keys_nodup

/-- A `for (const x of xs) n.set(f(x), g(x))` loop (from `n`) is `new Map` of the pairs. -/
theorem foldl_set {α} (m : JSMap K V) (xs : List α) (f : α → K) (g : α → V) :
    xs.foldl (fun acc x => acc.set (f x) (g x)) m = m.setAll (xs.map (fun x => (f x, g x))) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x rest ih => simp [List.foldl, setAll, ih]

omit [DecidableEq K] in
/-- Pigeonhole on keys: when every key of `a` is a key of `b`, `a` is no larger
(`[...a.keys()].every((k) => b.has(k))` → `a.size <= b.size`). -/
theorem length_keys_le_of_subset (a : JSMap K V) (b : JSMap K V) (h : ∀ k ∈ a.keys, k ∈ b.keys) :
    a.keys.length ≤ b.keys.length :=
  List.Nodup.length_le_of_subset a.keys_nodup h

omit [DecidableEq K] in
/-- …and strictly smaller when `b` has a key `a` lacks (so keys of `b` are keys of `a` when the
sizes are equal: `sameKeys` = equal sizes and one inclusion). -/
theorem length_keys_lt_of_subset_of_not_mem (a : JSMap K V) (b : JSMap K V) (h : ∀ k ∈ a.keys, k ∈ b.keys)
    (x : K) (hb : x ∈ b.keys) (hn : x ∉ a.keys) : a.keys.length < b.keys.length := by
  classical
  have hsub : a.keys ⊆ b.keys.erase x := by
    intro y hy
    have hyx : y ≠ x := fun e => hn (e ▸ hy)
    exact (List.mem_erase_of_ne hyx).2 (h y hy)
  have h1 := List.Nodup.length_le_of_subset a.keys_nodup hsub
  have h2 : (b.keys.erase x).length = b.keys.length - 1 := by rw [List.length_erase]; simp [hb]
  have h3 : 1 ≤ b.keys.length := List.length_pos_of_mem hb
  omega

omit [DecidableEq K] in
/-- A key of `m` is the key of an entry (`keys` lists the entries' keys), so an invariant over
the entries, `[...m].every(([k, v]) => …)`, applies to every key tested with `m.has(k)`. -/
theorem entry_of_mem_keys {m : JSMap K V} {k : K} (h : k ∈ m.keys) : ∃ v, (k, v) ∈ m.entries := by
  simp only [keys, List.mem_map] at h
  obtain ⟨⟨k', v⟩, hp, rfl⟩ := h
  exact ⟨v, hp⟩

omit [DecidableEq K] in
/-- A value of `m` is the value of an entry, so an invariant over the entries applies to
`[...m.values()]`. -/
theorem entry_of_mem_values {m : JSMap K V} {v : V} (h : v ∈ m.values) : ∃ k, (k, v) ∈ m.entries := by
  simp only [values, List.mem_map] at h
  obtain ⟨⟨k, v'⟩, hp, rfl⟩ := h
  exact ⟨k, hp⟩

omit [DecidableEq K] in
/-- The key of an entry is a key (`[...m].some(([j]) => j === k)` is `m.has(k)`). -/
theorem mem_keys_of_mem_entries {m : JSMap K V} {p : K × V} (h : p ∈ m.entries) : p.1 ∈ m.keys :=
  List.mem_map_of_mem h

end JSMap

/-- A JS `Set` with primitive elements: its elements in insertion order, distinct. -/
structure JSSet (T : Type) where
  elems : List T
  nodup : elems.Nodup

namespace JSSet
variable {T : Type}
/-- `s.size` -/
def size (s : JSSet T) : Int := s.elems.length
/-- `new Set()`, and `s.clear()` (on a fresh local). -/
def empty : JSSet T := ⟨[], List.nodup_nil⟩
instance : Inhabited (JSSet T) := ⟨empty⟩
theorem ext_elems {a b : JSSet T} (h : a.elems = b.elems) : a = b := by cases a; cases b; simp_all
instance [DecidableEq T] : DecidableEq (JSSet T) := fun a b =>
  if h : a.elems = b.elems then isTrue (ext_elems h) else isFalse (fun e => h (e ▸ rfl))
instance [Repr T] : Repr (JSSet T) := ⟨fun s _ => "new Set(" ++ reprArg s.elems ++ ")"⟩
variable [DecidableEq T]
/-- `s.has(x)` -/
def has (s : JSSet T) (x : T) : Bool := decide (x ∈ s.elems)
/-- `s.add(x)` (on a fresh copy): appended unless present (then the set is unchanged). -/
def add (s : JSSet T) (x : T) : JSSet T :=
  if h : x ∈ s.elems then s else ⟨s.elems ++ [x], by
    rw [List.nodup_append]; refine ⟨s.nodup, by simp, ?_⟩; intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact h ha⟩
/-- `s.delete(x)` as a statement on a fresh local. -/
def delete (s : JSSet T) (x : T) : JSSet T := ⟨s.elems.filter (fun y => !JS.eq y x), s.nodup.sublist List.filter_sublist⟩
/-- `add` of each element in turn. -/
def addAll (s : JSSet T) : List T → JSSet T
  | [] => s
  | x :: rest => (s.add x).addAll rest
/-- `new Set(xs)`: first occurrences, in order. -/
def ofList (xs : List T) : JSSet T := empty.addAll xs

theorem has_def (s : JSSet T) (x : T) : s.has x = decide (x ∈ s.elems) := rfl
theorem has_eq_true_iff (s : JSSet T) (x : T) : s.has x = true ↔ x ∈ s.elems := by simp [has]
theorem has_eq_false_iff (s : JSSet T) (x : T) : s.has x = false ↔ x ∉ s.elems := by simp [has]
theorem elems_add (s : JSSet T) (x : T) : (s.add x).elems = if x ∈ s.elems then s.elems else s.elems ++ [x] := by
  unfold add; split <;> simp_all
theorem mem_add (s : JSSet T) (x y : T) : y ∈ (s.add x).elems ↔ y = x ∨ y ∈ s.elems := by
  rw [elems_add]; by_cases h : x ∈ s.elems <;> simp [h] <;> grind
theorem elems_delete (s : JSSet T) (x : T) : (s.delete x).elems = s.elems.filter (fun y => !JS.eq y x) := rfl
omit [DecidableEq T] in
theorem size_eq (s : JSSet T) : s.size = (s.elems.length : Int) := rfl
omit [DecidableEq T] in
theorem elems_empty : (empty : JSSet T).elems = [] := rfl
theorem addAll_nil (s : JSSet T) : s.addAll [] = s := rfl
theorem addAll_cons (s : JSSet T) (x : T) (xs) : s.addAll (x :: xs) = (s.add x).addAll xs := rfl
theorem ofList_eq (xs : List T) : ofList xs = empty.addAll xs := rfl
omit [DecidableEq T] in
theorem nodup_elems (s : JSSet T) : s.elems.Nodup := s.nodup
theorem mem_elems_addAll (s : JSSet T) (xs : List T) (y : T) : y ∈ (s.addAll xs).elems ↔ y ∈ s.elems ∨ y ∈ xs := by
  induction xs generalizing s with
  | nil => simp [addAll]
  | cons x rest ih => rw [addAll_cons, ih, mem_add]; simp; grind
theorem mem_delete (s : JSSet T) (x y : T) : y ∈ (s.delete x).elems ↔ ¬ y = x ∧ y ∈ s.elems := by
  simp [elems_delete, JS.eq]; exact and_comm
/-- `new Set(xs).size <= xs.length` -/
theorem length_addAll_le (s : JSSet T) (xs : List T) : (s.addAll xs).elems.length ≤ s.elems.length + xs.length := by
  induction xs generalizing s with
  | nil => simp [addAll]
  | cons q rest ih =>
    rw [addAll_cons]
    have := ih (s.add q)
    rw [elems_add] at this
    split at this <;> simp at * <;> omega
theorem elems_addAll_of_nodup (s : JSSet T) (xs : List T) (h : (s.elems ++ xs).Nodup) :
    (s.addAll xs).elems = s.elems ++ xs := by
  induction xs generalizing s with
  | nil => simp [addAll]
  | cons q rest ih =>
    rw [addAll_cons]
    have hq : q ∉ s.elems := by
      simp only [List.nodup_append, List.nodup_cons] at h
      intro hk; exact h.2.2 _ hk _ (List.mem_cons_self ..) rfl
    have he : (s.add q).elems = s.elems ++ [q] := by rw [elems_add]; simp [hq]
    rw [ih, he]; · simp
    rw [he]; simpa using h
/-- `new Set(xs)` of distinct elements has exactly them, in order (`distinct(xs)` → `new Set(xs).size === xs.length`). -/
theorem elems_ofList_of_nodup (xs : List T) (h : xs.Nodup) : (empty.addAll xs).elems = xs := by
  rw [elems_addAll_of_nodup] <;> simp_all [elems_empty]
/-- A `for (const x of xs) n.add(f(x))` loop (from `n`) is `new Set` of the images. -/
theorem foldl_add {α} (s : JSSet T) (xs : List α) (f : α → T) :
    xs.foldl (fun acc x => acc.add (f x)) s = s.addAll (xs.map f) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x rest ih => simp [List.foldl, addAll, ih]
/-- `for (const x of xs) n.add(x)` (the elements themselves): `new Set` of the list. -/
theorem foldl_add_self (s : JSSet T) (xs : List T) :
    xs.foldl (fun acc x => acc.add x) s = s.addAll xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x rest ih => simp [List.foldl, addAll, ih]

omit [DecidableEq T] in
/-- Pigeonhole: a Set whose elements are all in `b` is no larger
(`[...a].every((x) => b.has(x))` → `a.size <= b.size`). -/
theorem length_le_of_subset (a b : JSSet T) (h : ∀ x ∈ a.elems, x ∈ b.elems) :
    a.elems.length ≤ b.elems.length :=
  List.Nodup.length_le_of_subset a.nodup h

omit [DecidableEq T] in
/-- …and strictly smaller when `b` has an element `a` lacks: with equal sizes, one inclusion
gives the other (`sameMembers(a, b)` = `a.size === b.size && [...a].every((x) => b.has(x))`). -/
theorem length_lt_of_subset_of_not_mem (a b : JSSet T) (h : ∀ y ∈ a.elems, y ∈ b.elems)
    (x : T) (hb : x ∈ b.elems) (hn : x ∉ a.elems) : a.elems.length < b.elems.length := by
  classical
  have hsub : a.elems ⊆ b.elems.erase x := by
    intro y hy
    have hyx : y ≠ x := fun e => hn (e ▸ hy)
    exact (List.mem_erase_of_ne hyx).2 (h y hy)
  have h1 := List.Nodup.length_le_of_subset a.nodup hsub
  have h2 : (b.elems.erase x).length = b.elems.length - 1 := by rw [List.length_erase]; simp [hb]
  have h3 : 1 ≤ b.elems.length := List.length_pos_of_mem hb
  omega
end JSSet

/-! ## Automation

Normal form: `get`, `keys`, `values` and `size` of a map stay atomic; Bool `has` becomes a
membership; deletes become list filters (`vreact_simp`).  `keys_set` is `grind`-only: as a
rewrite rule it would put an `if` into the `Nodup` sources of `vreact_subperm`.  The two Option
facts at the end (`o!`, `o ?? d`) serve every optional value, `m.get(k)` among them. -/

attribute [vreact_simp] JSMap.has_def JSMap.get_set JSMap.get_delete
  JSMap.get_empty JSMap.mem_keys_set JSMap.size_set JSMap.size_delete
  JSMap.keys_empty JSMap.size_empty JSMap.values_empty JSMap.entries_empty
  JSMap.setAll_nil JSMap.setAll_cons JSMap.ofList_eq JSMap.mem_values_set
  JSMap.mem_keys_setAll JSMap.keys_delete JSMap.entries_delete JSMap.length_keys_set
  JSMap.mem_entries_set JSMap.foldl_set
attribute [vreact_simp] decide_eq_decide decide_not
attribute [grind =] JSMap.get_set JSMap.get_delete JSMap.get_empty JSMap.mem_keys_set JSMap.mem_keys_delete
  JSMap.size_set JSMap.size_delete JSMap.mem_values_set JSMap.has_eq_true_iff
  JSMap.get_ofList_of_nodup JSMap.keys_set JSMap.keys_delete JSMap.keys_empty JSMap.length_keys_set
  JSMap.mem_entries_set
attribute [grind →] JSMap.get_of_mem_entries JSMap.mem_values_of_mem_delete JSMap.mem_values_of_get
  JSMap.mem_keys_of_get JSMap.mem_entries_of_get JSMap.mem_entries_setAll JSMap.mem_values_setAll
  JSMap.entry_of_mem_keys JSMap.entry_of_mem_values JSMap.mem_keys_of_mem_entries
attribute [vreact_simp] JSMap.delete_empty
attribute [grind =] JSMap.delete_empty JSMap.values_empty JSMap.entries_empty
grind_pattern JSMap.keys_nodup => m.keys
grind_pattern JSMap.size_nonneg => m.size
grind_pattern JSMap.size_eq_length_keys => m.size
grind_pattern JSMap.get_eq_none_iff => m.get k
grind_pattern JSMap.nodup_entries_fst => m.entries
grind_pattern JSMap.nodup_map_values_of_key => (List.map f (JSMap.values m)).Nodup
grind_pattern JSMap.length_entries => m.entries.length
grind_pattern JSMap.length_values => m.values.length
grind_pattern JSMap.size_setAll_le => (m.setAll xs).size
grind_pattern JSMap.entries_ofList_of_nodup => (JSMap.empty.setAll xs).entries
grind_pattern JSMap.size_ofList_of_nodup => (JSMap.empty.setAll xs).size
-- (for each element of the list the index is built from; the key function's `Nodup` is the
-- distinct-keys fact `distinct(xs, (x) => x.id)` once `h` is instantiated and beta-reduced)
grind_pattern JSMap.get_ofList_map_of_nodup => (JSMap.empty.setAll (xs.map h)), x ∈ xs
-- pigeonhole (inclusion of distinct keys bounds the size), for the pairs of maps whose sizes
-- occur; the strict form for a key of `b` tested in `a`
grind_pattern JSMap.length_keys_le_of_subset => a.keys.length, b.keys.length
grind_pattern JSMap.length_keys_lt_of_subset_of_not_mem => x ∈ a.keys, b.keys.length

attribute [vreact_simp] JSSet.has_def JSSet.elems_add JSSet.elems_delete
  JSSet.size_eq JSSet.elems_empty JSSet.addAll_nil JSSet.addAll_cons JSSet.ofList_eq
  JSSet.mem_elems_addAll JSSet.foldl_add JSSet.foldl_add_self
attribute [grind =] JSSet.mem_elems_addAll JSSet.mem_add JSSet.mem_delete JSSet.elems_empty
grind_pattern JSSet.nodup_elems => s.elems
grind_pattern JSSet.length_addAll_le => (s.addAll xs).elems.length
grind_pattern JSSet.elems_ofList_of_nodup => (JSSet.empty.addAll xs).elems
grind_pattern JSSet.length_le_of_subset => a.elems.length, b.elems.length
grind_pattern JSSet.length_lt_of_subset_of_not_mem => x ∈ a.elems, b.elems.length

/-- Distinct keys as a contract: `vreact_contracts` adds it as a hypothesis wherever `m.keys`
occurs (`vreact_subperm` moves `Nodup` facts from hypotheses through list chains). -/
theorem JSMap.keys.post {K V : Type} (m : JSMap K V) : m.keys.Nodup := m.nodup
theorem JSMap.entries.post {K V : Type} (m : JSMap K V) : (m.entries.map Prod.fst).Nodup := m.nodup
theorem JSSet.elems.post {T : Type} (s : JSSet T) : s.elems.Nodup := s.nodup

/-- `o!` (non-null assertion, `Option.get o h`): the value is the content of `o`. -/
theorem opt_eq_some_get {α} (o : Option α) (h : o.isSome = true) : o = some (o.get h) := by cases o <;> simp_all
grind_pattern opt_eq_some_get => o.get h
/-- `o ?? d` (`Option.getD o d`): the default, or the content of `o`. -/
theorem getD_mem_or {α} (o : Option α) (d : α) : o.getD d = d ∨ o = some (o.getD d) := by cases o <;> simp
grind_pattern getD_mem_or => o.getD d

end VReact.JS
