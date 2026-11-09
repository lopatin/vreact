import VTS.model.Defs
open VReact

@[vreact_simp] theorem openQty_nil : VTS.model.openQty [] = 0 := by
  unfold VTS.model.openQty
  rfl

theorem openQty_foldl_acc (os : List VTS.model.Order) (a : Int) :
    os.foldl (fun (n : Int) (o : VTS.model.Order) => (n + o.qty)) a
      = a + os.foldl (fun (n : Int) (o : VTS.model.Order) => (n + o.qty)) 0 := by
  induction os generalizing a with
  | nil => simp
  | cons o os ih =>
    simp only [List.foldl_cons]
    rw [ih (a + o.qty), ih (0 + o.qty)]
    omega

/-- Peeling off the first order. No induction: lemma `openQty_foldl_acc` does the work. -/
@[vreact_simp] theorem openQty_cons (o : VTS.model.Order) (os : List VTS.model.Order) :
    VTS.model.openQty (o :: os) = o.qty + VTS.model.openQty os := by
  unfold VTS.model.openQty
  simp only [List.foldl_cons]
  -- ⊢ List.foldl … (0 + o.qty) os = o.qty + List.foldl … 0 os
  rw [openQty_foldl_acc os (0 + o.qty)]
  omega

/-- The total of two lists joined is the sum of their totals. -/
@[vreact_simp] theorem openQty_append (xs ys : List VTS.model.Order) :
    VTS.model.openQty (xs ++ ys) = VTS.model.openQty xs + VTS.model.openQty ys := by
  induction xs with
  | nil => simp [openQty_nil]
  | cons x xs ih =>
    -- ⊢ openQty (x :: xs ++ ys) = openQty (x :: xs) + openQty ys
    rw [List.cons_append, openQty_cons, openQty_cons, ih]
    -- ⊢ x.qty + (openQty xs + openQty ys) = x.qty + openQty xs + openQty ys
    omega

/-! ## The working orders are a Map

`openQty([...u.orders.values()])` is `openQty u.orders.values`: the orders of the Map's entries,
in insertion order. `place` sets an order under a fresh id, which appends an entry; `cancel`
deletes one, which filters the entries. -/

namespace OrdersMap
open VReact.JS VTS.model

/-- Replacing the entry of a present key (keys are distinct, so there is one): the total
changes by the difference of the two quantities. -/
theorem openQty_map_update (l : List (Int × Order)) (k : Int) (v o : Order)
    (hn : (l.map Prod.fst).Nodup) (hm : (k, o) ∈ l) :
    openQty ((l.map (fun p => if p.1 = k then (k, v) else p)).map Prod.snd)
      = openQty (l.map Prod.snd) - o.qty + v.qty := by
  induction l with
  | nil => simp at hm
  | cons p l ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hp, hn⟩ := hn
    by_cases hk : p.1 = k
    · -- p is the entry of k: the rest has no entry of k
      have hpo : p = (k, o) := by
        rcases List.mem_cons.mp hm with h | h
        · exact h.symm
        · exfalso; apply hp; rw [hk]; exact List.mem_map.mpr ⟨(k, o), h, rfl⟩
      have hrest : l.map (fun p => if p.1 = k then (k, v) else p) = l := by
        conv => rhs; rw [← List.map_id l]
        apply List.map_congr_left
        intro q hq
        have : q.1 ≠ k := by
          intro e; apply hp; rw [hk, ← e]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
        simp [this]
      simp only [List.map_cons, hk, ite_true, hrest, openQty_cons]
      rw [hpo]
      simp only
      omega
    · have hm' : (k, o) ∈ l := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd (by rw [← h]) hk
        · exact h
      simp only [List.map_cons, hk, ite_false, openQty_cons]
      rw [ih hn hm']
      omega

/-- `place` and the total: `set` on a key that is not in use appends the entry, so the total
grows by its quantity; on a key in use it replaces that entry's order in place. -/
theorem openQty_set (m : JSMap Int Order) (k : Int) (v : Order) :
    openQty (m.set k v).values
      = if k ∈ m.keys then openQty m.values - ((m.get k).getD v).qty + v.qty
        else openQty m.values + v.qty := by
  unfold JSMap.values
  rw [JSMap.entries_set]
  by_cases h : k ∈ m.keys
  · obtain ⟨o, ho⟩ := JSMap.entry_of_mem_keys h
    rw [JSMap.get_of_mem_entries ho]
    simp only [h, ite_true, Option.getD_some]
    exact openQty_map_update m.entries k v o m.nodup ho
  · simp only [h, ite_false, List.map_append, openQty_append, List.map_cons, List.map_nil, openQty_cons, openQty_nil]
    omega

/-- Removing entries never raises the total, as long as no quantity is negative. -/
theorem openQty_filter_le (l : List (Int × Order)) (p : Int × Order → Bool)
    (h : ∀ q ∈ l, 0 ≤ q.2.qty) :
    openQty ((l.filter p).map Prod.snd) ≤ openQty (l.map Prod.snd) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq : 0 ≤ q.2.qty := h q (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    -- does the filter keep `q`?
    cases hp : p q
    · simp [hp, openQty_cons]; omega
    · simp [hp, openQty_cons]; omega

/-- `cancel`: deleting an entry never raises the total, as long as no quantity is negative. -/
theorem openQty_delete_le (m : JSMap Int Order) (k : Int) (h : ∀ q ∈ m.entries, 0 ≤ q.2.qty) :
    openQty (m.delete k).values ≤ openQty m.values := by
  unfold JSMap.values
  rw [JSMap.entries_delete]
  exact openQty_filter_le _ _ h

end OrdersMap

-- Let `grind` use them whenever it sees the total of a Map after a `set` or a `delete`: it splits
-- on the `if` of `openQty_set` (is the key in use? not when it is nextId, by the invariant), and
-- proves the side condition of `openQty_delete_le` from the invariant (valid orders).
grind_pattern OrdersMap.openQty_set => VTS.model.openQty (VReact.JS.JSMap.values (VReact.JS.JSMap.set m k v))
grind_pattern OrdersMap.openQty_delete_le => VTS.model.openQty (VReact.JS.JSMap.values (VReact.JS.JSMap.delete m k))
