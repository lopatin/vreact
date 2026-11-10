import VTS.Base_.Defs
open VReact

theorem foldl_cents_init (xs : List VTS.Base_.Line) (a : Int) :
    xs.foldl (fun (acc' : Int) (l : VTS.Base_.Line) => (acc' + l.cents)) a
      = a + xs.foldl (fun (acc' : Int) (l : VTS.Base_.Line) => (acc' + l.cents)) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons]; rw [ih (a + y.cents), ih (0 + y.cents)]; omega

@[vreact_simp, grind =] theorem total_cons (l : VTS.Base_.Line) (xs : List VTS.Base_.Line) :
    VTS.Base_.total (l :: xs) = VTS.Base_.total xs + l.cents := by
  unfold VTS.Base_.total; simp only [List.foldl_cons]; rw [foldl_cents_init]; omega

@[vreact_simp, grind =] theorem total_singleton_append (l : VTS.Base_.Line) (xs : List VTS.Base_.Line) :
    VTS.Base_.total ([l] ++ xs) = VTS.Base_.total xs + l.cents := by
  simp only [List.singleton_append]; exact total_cons l xs

@[vreact_simp, grind =] theorem total_nil : VTS.Base_.total [] = 0 := by
  unfold VTS.Base_.total; simp
