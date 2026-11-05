import VTS.sums.Defs
open VReact

theorem foldl_cents_init (xs : List VTS.sums.Line) (a : Int) :
    xs.foldl (fun (acc' : Int) (l : VTS.sums.Line) => (acc' + l.cents)) a
      = a + xs.foldl (fun (acc' : Int) (l : VTS.sums.Line) => (acc' + l.cents)) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons]; rw [ih (a + y.cents), ih (0 + y.cents)]; omega

@[vreact_simp, grind =] theorem total_cons (l : VTS.sums.Line) (xs : List VTS.sums.Line) :
    VTS.sums.total (l :: xs) = VTS.sums.total xs + l.cents := by
  unfold VTS.sums.total; simp only [List.foldl_cons]; rw [foldl_cents_init]; omega

@[vreact_simp, grind =] theorem total_singleton_append (l : VTS.sums.Line) (xs : List VTS.sums.Line) :
    VTS.sums.total ([l] ++ xs) = VTS.sums.total xs + l.cents := by
  simp only [List.singleton_append]; exact total_cons l xs

@[vreact_simp, grind =] theorem total_nil : VTS.sums.total [] = 0 := by
  unfold VTS.sums.total; simp
