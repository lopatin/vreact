import VTS.TodoApp.Defs
open VReact

/-- A user lemma: available (and usable via `@[vreact_simp]` / `@[grind]`) to every
obligation of the TodoApp module's components. -/
theorem visible_sublist (ts : List VTS.types.Todo) (f : VTS.types.Filter) :
    (VTS.TodoApp.visible ts f).Sublist ts := by
  unfold VTS.TodoApp.visible
  split <;> simp
