theorem foldl_add_acc (ys : List Int) (a : Int) :
    ys.foldl (fun a b => a + b) a = a + ys.foldl (fun a b => a + b) 0 := by
  induction ys generalizing a with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons]; rw [ih (a + y), ih (0 + y)]; omega
