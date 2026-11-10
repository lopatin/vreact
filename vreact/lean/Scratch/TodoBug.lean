import VReact
open VReact

namespace TodoDemo

structure Todo where
  id : Int
  text : String
  done : Bool
deriving Repr, DecidableEq

namespace TodoItem
structure Props where
  todo : Todo
structure Cb (d : Props) (E : Type) : Type where
  onToggle : (id : Int) → (id = d.todo.id) → E
  onDelete : (id : Int) → (id = d.todo.id) → E
structure State where
@[vreact_simp] def pre (_d : Props) : Prop := True
@[vreact_simp] def inv (_d : Props) (_s : State) : Prop := True
def init (_d : Props) (_h : pre _d) : State := {}
abbrev spec : Spec where
  name := "TodoItem"
  D := Props
  Cb := Cb
  S := State
  pre := pre
  inv := inv
  init := init
  init_inv := by vreact_auto
  stable := by vreact_auto
def render {E : Type} (d : Props) (cb : Cb d E) (s : State) (hpre : pre d) (hinv : inv d s) : VNode State E (inv d) s :=
    let props := d
    VNode.elem "li" [] [] (VList.ofList [
      VNode.elem "input" [⟨"type", .str "checkbox"⟩, ⟨"checked", .bool props.todo.done⟩]
        [Handler.discrete "change" (fun ev => { emit := some (cb.onToggle props.todo.id (by vreact_auto)) }) (by vreact_auto) (by decide)] VList.nil,
      VNode.text props.todo.text,
      VNode.elem "button" []
        [Handler.discrete "click" (fun ev => { emit := some (cb.onDelete props.todo.id (by vreact_auto)) }) (by vreact_auto) (by decide)]
        (VList.ofList [VNode.text "×"])])
def component : Component spec := ⟨fun d cb s hpre hinv => render d cb s hpre hinv⟩
end TodoItem

namespace TodoApp
structure Props where
structure State where
  todos : List Todo
  nextId : Int
  draft : String
@[vreact_simp] def pre (_d : Props) : Prop := True
@[vreact_simp] def inv (_d : Props) (s : State) : Prop :=
  (s.todos.map (fun t => t.id)).Nodup ∧ (∀ t ∈ s.todos, t.id < s.nextId) ∧ JS.strLen s.draft ≤ 100
@[vreact_simp] def init (_d : Props) (_h : pre _d) : State := { todos := [], nextId := 1, draft := "" }
abbrev spec : Spec where
  name := "TodoApp"
  D := Props
  Cb := NoCb
  S := State
  pre := pre
  inv := inv
  init := init
  init_inv := by vreact_auto
  stable := by vreact_auto

def render {E : Type} (d : Props) (cb : NoCb d E) (s : State) (hpre : pre d) (hinv : inv d s) : VNode State E (inv d) s :=
    let todos := s.todos
    let nextId := s.nextId
    let draft := s.draft
    let remaining := JS.len (todos.filter (fun t => !t.done))
    VNode.elem "div" [] [] (VList.ofList [
      VNode.elem "input" [⟨"value", .str draft⟩]
        [Handler.discrete "change" (fun ev =>
          if decide (JS.strLen ev.value ≤ 100) then { updates := [fun st => { st with draft := ev.value }] } else { updates := [] })
          (by vreact_auto) (by decide)] VList.nil,
      VNode.elem "button" []
        [Handler.discrete "click" (fun ev =>
          let t := JS.trim draft
          if decide (JS.strLen t > 0) then { updates :=
              [fun st => { st with todos := todos ++ [{ id := nextId, text := t, done := false }] },

               fun st => { st with draft := "" }] } else { updates := [] })
          (by vreact_auto) (by decide)]
        (VList.ofList [VNode.text "Add"]),
      VNode.keyedMap todos (fun t => Key.int t.id) (fun t h_t => (
        TodoItem.component.node ({ todo := t } : TodoItem.Props)
          (TodoItem.Cb.mk
            (fun id h => Emit.mk
              ({ updates := [fun st => { st with todos := todos.map (fun x => if decide (x.id = id) then { x with done := !x.done } else x) }] })
              (by vreact_auto))
            (fun id h => Emit.mk
              ({ updates := [fun st => { st with todos := todos.filter (fun x => !decide (x.id = id)) }] })
              (by vreact_auto)))
          (by vreact_auto)))
        (by vreact_auto),
      VNode.text (JS.str remaining ++ " left")])
def component : Component spec := ⟨fun d cb s hpre hinv => render d cb s hpre hinv⟩
end TodoApp
#print axioms TodoApp.component
end TodoDemo
