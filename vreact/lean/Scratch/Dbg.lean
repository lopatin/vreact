import VReact
open VReact
structure Todo where
  id : Int
  text : String
  done : Bool
deriving Repr, DecidableEq
structure State where
  todos : List Todo
  nextId : Int
  draft : String
@[vreact_simp] def inv (s : State) : Prop :=
  (s.todos.map (fun t => t.id)).Nodup ∧ (∀ t ∈ s.todos, t.id < s.nextId) ∧ JS.strLen s.draft ≤ 100

example (s : State) (hinv : inv s) : ∀ (ev : DomEvent), inv ((if decide (JS.strLen (JS.trim s.draft) > 0) then ({ updates :=
              [fun st => { st with todos := s.todos ++ [{ id := s.nextId, text := JS.trim s.draft, done := false }] },
               fun st => { st with nextId := s.nextId + 1 },
               fun st => { st with draft := "" }] } : Outcome State Empty) else { updates := [] }).apply s) := by
  intro ev
  vreact_norm
  split <;> grind

example (s : State) (hinv : inv s) (id : Int) : inv (({ updates := [fun st => { st with todos := s.todos.filter (fun x => !decide (x.id = id)) }] } : Outcome State Empty).apply s) := by
  vreact_norm
  grind

example (s : State) (hinv : inv s) (id : Int) : inv (({ updates := [fun st => { st with todos := s.todos.map (fun x => if decide (x.id = id) then { x with done := !x.done } else x) }] } : Outcome State Empty).apply s) := by
  vreact_norm
  grind
