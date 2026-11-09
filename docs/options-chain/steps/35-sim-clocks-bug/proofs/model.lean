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

/-- The total of two lists joined is the sum of their totals (`place` appends an order). -/
@[vreact_simp] theorem openQty_append (xs ys : List VTS.model.Order) :
    VTS.model.openQty (xs ++ ys) = VTS.model.openQty xs + VTS.model.openQty ys := by
  induction xs with
  | nil => simp [openQty_nil]
  | cons x xs ih =>
    -- ⊢ openQty (x :: xs ++ ys) = openQty (x :: xs) + openQty ys
    rw [List.cons_append, openQty_cons, openQty_cons, ih]
    -- ⊢ x.qty + (openQty xs + openQty ys) = x.qty + openQty xs + openQty ys
    omega

/-- Removing orders never raises the total, as long as no quantity is negative (`cancel`). -/
theorem openQty_filter_le (p : VTS.model.Order → Bool) (os : List VTS.model.Order)
    (h : ∀ o ∈ os, 0 ≤ o.qty) :
    VTS.model.openQty (os.filter p) ≤ VTS.model.openQty os := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have ho : 0 ≤ o.qty := h o (by simp)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    -- does the filter keep `o`?
    cases hp : p o
    · -- no:  openQty (filter p os) ≤ o.qty + openQty os
      simp [hp, openQty_cons]
      omega
    · -- yes: o.qty + openQty (filter p os) ≤ o.qty + openQty os
      simp [hp, openQty_cons]
      omega

-- Not a rewrite rule (an inequality with a side condition): let `grind` use it whenever it
-- sees the total of a filtered list; it proves the side condition from the invariant.
grind_pattern openQty_filter_le => VTS.model.openQty (List.filter p os)

