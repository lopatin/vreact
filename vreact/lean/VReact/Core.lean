import VReact.JS
import VReact.Attr
/-!
# VReact.Core — a semantic model of React components

This file fixes *what a React component means* for the verifier.

## State and the update queue

A component's hook state (all `useState`/`useReducer` slots) is a value `s : S`.
Calling a setter does **not** change state immediately: React appends an update
to a queue and processes the queue after the handler returns.  We model one
setter call as an `Update S := S → S`:

* `setX(v)`        ↦ `fun st => { st with x := v }`  where `v` was computed from
                       the *render snapshot* (the closure's captured values);
* `setX(f)`        ↦ `fun st => { st with x := f st.x }` (functional update);
* `dispatch(a)`    ↦ `fun st => { st with r := reducer st.r a }`.

`Outcome.apply` folds the queue over the state, which reproduces React's
batching exactly — e.g. `setN(n + 1); setN(n + 1)` increments once while
`setN(m => m + 1); setN(m => m + 1)` increments twice.

## Snapshots, discrete events and robustness

React flushes the updates of a *discrete* event (click, input, keydown, submit…;
exactly React's `DiscreteEventPriority` events) synchronously, so the next
discrete event always runs a handler from the latest committed render, whose
captured snapshot equals the current state.  A discrete handler therefore only
has to preserve the invariant **from its snapshot** — unless its component has
*deferred* updates (below).

Continuous- and default-priority events (mousemove, scroll, transitionend,
load, …), effects and asynchronous callbacks (timers, subscriptions) may run
while the snapshot is stale, and their updates are rendered later, so their
outcomes must be **robust**: preserve the invariant from *every* state
satisfying it.

React keeps one update queue per hook and *rebases*: a later discrete update is
rendered first, skipping a pending lower-priority one, and is then re-applied on
top of it.  So in a component with deferred updates (`RebaseSafe`), a discrete
outcome must preserve the invariant from every invariant state that agrees with
the snapshot on all fields no deferred source writes.

## Rendering

`render` is a pure function of `(props, state)` producing a `VNode` tree.  The
tree is *proof-carrying*: every handler stores the proof that its outcome is
safe, every child-component node stores the proof of the child's precondition,
and every keyed list stores the proof that its keys are distinct.  A render
function that type-checks is therefore a render that can only ever offer
invariant-preserving interactions to the user.

## Composition

A child receives callbacks from its parent.  The parent hands over, for each
callback, a function producing an `Emit` — a parent outcome *packaged with the
proof* that applying it to the parent's snapshot preserves the parent's
invariant.  The child must prove the callback's declared precondition before it
may call it.  This is assume/guarantee reasoning, checked by the type checker.
-/
namespace VReact

/-! ## Keys, attributes, events -/

/-- React keys.  Within one list all keys come from a single expression, hence a
single static type, so `int` and `str` keys never mix (where React would
coerce both to strings). -/
inductive Key where
  | int (i : Int)
  | str (s : JS.Str)
deriving DecidableEq, Repr

inductive AttrVal where
  | str (s : JS.Str)
  | int (i : Int)
  | bool (b : Bool)
  | num (f : Float)
  | none

structure Attr where
  name : String
  val : AttrVal

/-- The information a handler can read from a DOM event.  The model makes no
assumption about its contents: every proof must hold for all events. -/
structure DomEvent where
  /-- `e.target.value` -/
  value : JS.Str := ⟨[]⟩
  /-- `e.target.checked` -/
  checked : Bool := false
  /-- `e.key` -/
  key : JS.Str := ⟨[]⟩

/-- React's continuous-priority events (ReactDOMEventListener.getEventPriority). -/
def continuousEvents : List String :=
  ["drag", "dragenter", "dragexit", "dragleave", "dragover", "mousemove", "mouseout",
   "mouseover", "pointermove", "pointerout", "pointerover", "scroll", "toggle",
   "touchmove", "wheel", "mouseenter", "mouseleave", "pointerenter", "pointerleave"]

/-- The handler names (React prop `onX` lower-cased; `onDoubleClick` ↦ `dblclick`)
whose native events all have React 18's `DiscreteEventPriority`
(react-dom 18.3.1 `getEventPriority`).  A whitelist: every other event —
continuous *and* default priority (`transitionend`, `load`, media events, …) —
is not discrete, and its handlers must be robust. -/
def discreteEvents : List String :=
  ["auxclick", "cancel", "click", "close", "contextmenu", "copy", "cut", "dragend",
   "dragstart", "drop", "input", "invalid", "keydown", "keypress", "keyup", "mousedown",
   "mouseup", "paste", "pause", "play", "pointercancel", "pointerdown", "pointerup",
   "ratechange", "reset", "resize", "seeked", "submit", "touchcancel", "touchend",
   "touchstart", "volumechange", "dblclick", "focus", "blur", "change", "beforeinput",
   "compositionstart", "compositionend", "compositionupdate"]

def isDiscrete (ev : String) : Bool := discreteEvents.contains ev

/-! ## Updates and outcomes -/

/-- One queued state update (one setter / dispatch call). -/
abbrev Update (S : Type) := S → S

/-- The result of running a handler: the queued updates on the owning component,
and at most one invocation of a parent callback. -/
structure Outcome (S E : Type) where
  updates : List (Update S) := []
  emit : Option E := none

/-- Process the update queue (React's `processUpdateQueue`). -/
def Outcome.apply {S E : Type} (o : Outcome S E) (s : S) : S :=
  o.updates.foldl (fun s u => u s) s

@[simp] theorem Outcome.apply_nil {S E} (s : S) (e : Option E) :
    ({ updates := [], emit := e } : Outcome S E).apply s = s := rfl
@[simp] theorem Outcome.apply_cons {S E} (u : Update S) (us : List (Update S)) (e : Option E) (s : S) :
    ({ updates := u :: us, emit := e } : Outcome S E).apply s =
      ({ updates := us, emit := e } : Outcome S E).apply (u s) := rfl

/-- `o` preserves `inv` from every state satisfying it. -/
def Robust {S E : Type} (inv : S → Prop) (o : Outcome S E) : Prop :=
  ∀ s, inv s → inv (o.apply s)

/-- Rebasing (React 18 lanes).  In a component with *deferred* updates (timer
tasks, effects that set state, continuous/default-priority handlers), the hooks
those sources write may carry pending lower-priority updates when a discrete
event runs.  React renders the discrete updates first, skipping the pending ones,
and later re-applies them on top: the outcome of a discrete handler is applied to
the snapshot *or* to a state in which the deferred fields have other values.
`vary x` is the snapshot with the deferred fields replaced by `x`; every other
field (whose hook queue only ever holds synchronously flushed updates) equals the
snapshot.  `RebaseSafe inv vary o`: `o` keeps `inv` from every such state. -/
@[vreact_simp] def RebaseSafe {S E X : Type} (inv : S → Prop) (vary : X → S) (o : Outcome S E) : Prop :=
  ∀ x, inv (vary x) → inv (o.apply (vary x))

theorem RebaseSafe.at_snap {S E X : Type} {inv : S → Prop} {vary : X → S} {o : Outcome S E}
    {snap : S} (x₀ : X) (hx : vary x₀ = snap) (hs : inv snap) (h : RebaseSafe inv vary o) :
    inv (o.apply snap) := by
  cases hx; exact h x₀ hs

/-- With no deferred fields (`vary` constant) rebase-safety is snapshot safety;
with all fields deferred it is robustness. -/
theorem Robust.rebaseSafe {S E X : Type} {inv : S → Prop} {o : Outcome S E} (vary : X → S)
    (h : Robust inv o) : RebaseSafe inv vary o := fun x hx => h (vary x) hx

/-- A parent outcome packaged with the proof that it preserves the parent's
invariant when applied to the parent's snapshot. -/
def Emit (S E : Type) (inv : S → Prop) (snap : S) : Type :=
  { o : Outcome S E // inv (o.apply snap) }

/-! ## Handlers and effects -/

/-- An event handler attached to a host element. -/
inductive Handler (S E : Type) (inv : S → Prop) (snap : S) : Type where
  /-- Discrete events run against the current snapshot. -/
  | discrete (event : String) (run : DomEvent → Outcome S E)
      (ok : ∀ e, inv ((run e).apply snap)) (hd : isDiscrete event = true)
  /-- Continuous- and default-priority events may observe stale snapshots and are
  rendered later: robust, and no callbacks. -/
  | continuous (event : String) (run : DomEvent → Outcome S E)
      (ok : ∀ e, Robust inv (run e)) (noEmit : ∀ e, (run e).emit = none)

def Handler.event {S E inv snap} : Handler S E inv snap → String
  | .discrete ev .. => ev
  | .continuous ev .. => ev

def Handler.run {S E inv snap} : Handler S E inv snap → DomEvent → Outcome S E
  | .discrete _ r .. => r
  | .continuous _ r .. => r

/-- A discrete handler of a component with deferred updates: its outcome is
checked `RebaseSafe` (every state React may rebase it onto), which in particular
covers the snapshot.  It may invoke a parent callback. -/
def Handler.rebased {S E X : Type} {inv : S → Prop} {snap : S} (event : String)
    (run : DomEvent → Outcome S E) (vary : X → S) (x₀ : X) (hx : vary x₀ = snap) (hs : inv snap)
    (ok : ∀ e, RebaseSafe inv vary (run e)) (hd : isDiscrete event = true) : Handler S E inv snap :=
  .discrete event run (fun e => RebaseSafe.at_snap x₀ hx hs (ok e)) hd

/-- Closes `o.emit = none` for the outcomes of robust handlers and effect setups:
the translator rejects parent callbacks there, so every branch ends in
`emit := none`.  (Not a user obligation: a failure is a translator bug.)
Let-bound locals are unfolded first (`zetaDelta`), so that `split` can case on
`match h : x with` where `x` is a render-local. -/
macro "vreact_noemit" : tactic =>
  `(tactic| (intros
             try simp (config := { zetaDelta := true, failIfUnchanged := false }) only []
             all_goals ((repeat' split) <;> (first | rfl | (simp_all; done)))))

/-- A dependency value of `useEffect`.  Objects are compared by identity in
React; the model treats them as "possibly changed" (`obj`), which only makes
effects fire more often — harmless because effect outcomes are robust. -/
inductive DepVal where
  | int (i : Int)
  | str (s : JS.Str)
  | bool (b : Bool)
  | obj
deriving DecidableEq, Repr

/-- A `useEffect`.  The body runs after commit when `deps` changed (always, when
`deps = none`).  Its synchronous updates and any asynchronous callbacks it
schedules (timers, subscriptions) must be robust and must not call parents. -/
structure Effect (S E : Type) (inv : S → Prop) where
  deps : Option (List DepVal)
  setup : Outcome S E
  setup_ok : Robust inv setup
  setup_noEmit : setup.emit = none
  tasks : List (DomEvent → Outcome S E) := []
  tasks_ok : ∀ t ∈ tasks, ∀ e, Robust inv (t e) ∧ (t e).emit = none

/-- Whether an effect fires, given its previous dependency values. -/
def Effect.fires {S E inv} (eff : Effect S E inv) (prev : Option (Option (List DepVal))) : Bool :=
  match prev, eff.deps with
  | none, _ => true                      -- first commit after mount
  | some _, none => true                 -- no dependency array
  | some none, some _ => true
  | some (some old), some new => old != new || new.contains .obj

/-! ## Component specifications -/

/-- Everything about a component except its view: props (data part `D`,
callback part `Cb`), state, precondition, invariant and initial state, together
with the two lifecycle obligations. -/
structure Spec : Type 1 where
  name : String
  /-- Data props (no functions). -/
  D : Type
  /-- Callback props, given the props data and the type `E` of parent outcomes. -/
  Cb : D → Type → Type
  /-- Hook state: one field per `useState`/`useReducer`. -/
  S : Type
  pre : D → Prop
  inv : D → S → Prop
  init : (d : D) → pre d → S
  /-- Mounting establishes the invariant. -/
  init_inv : ∀ d (h : pre d), inv d (init d h)
  /-- Re-rendering with new props keeps the state (React preserves state of a
  component at the same position): the invariant must survive prop changes. -/
  stable : ∀ d d' s, inv d s → pre d' → inv d' s

/-! ## The view tree -/

mutual
/-- A rendered tree, owned by a component with state type `S`, parent-outcome
type `E`, invariant `inv` and render snapshot `snap`. -/
inductive VNode : (S E : Type) → (S → Prop) → S → Type 1 where
  | empty {S E inv snap} : VNode S E inv snap
  | text {S E inv snap} (s : JS.Str) : VNode S E inv snap
  | elem {S E inv snap} (tag : String) (attrs : List Attr)
      (handlers : List (Handler S E inv snap)) (children : VList S E inv snap) : VNode S E inv snap
  /-- A keyed list (`xs.map(x => <li key={…}/>)`), keys pairwise distinct. -/
  | keyed {S E inv snap} (keys : List Key) (items : KList S E inv snap keys)
      (nodup : keys.Nodup) : VNode S E inv snap
  /-- A child component element `<C {...props}/>`. -/
  | comp {S E inv snap} (spec : Spec) (d : spec.D) (cb : spec.Cb d (Emit S E inv snap))
      (pre : spec.pre d)
      (render : (s : spec.S) → spec.inv d s → VNode spec.S (Emit S E inv snap) (spec.inv d) s) :
      VNode S E inv snap
  /-- The effects declared by the owning component (attached at its root). -/
  | withEffects {S E inv snap} (effects : List (Effect S E inv)) (body : VNode S E inv snap) :
      VNode S E inv snap

inductive VList : (S E : Type) → (S → Prop) → S → Type 1 where
  | nil {S E inv snap} : VList S E inv snap
  | cons {S E inv snap} (head : VNode S E inv snap) (tail : VList S E inv snap) : VList S E inv snap

inductive KList : (S E : Type) → (S → Prop) → S → List Key → Type 1 where
  | nil {S E inv snap} : KList S E inv snap []
  | cons {S E inv snap ks} (k : Key) (head : VNode S E inv snap) (tail : KList S E inv snap ks) :
      KList S E inv snap (k :: ks)
end

def VList.ofList {S E inv snap} : List (VNode S E inv snap) → VList S E inv snap
  | [] => .nil
  | x :: xs => .cons x (VList.ofList xs)

def KList.ofList {S E inv snap} : (xs : List (Key × VNode S E inv snap)) → KList S E inv snap (xs.map Prod.fst)
  | [] => .nil
  | (k, n) :: xs => .cons k n (KList.ofList xs)

/-- A keyed list built from `(key, node)` pairs. -/
def VNode.keyedOf {S E inv snap} (xs : List (Key × VNode S E inv snap))
    (nodup : (xs.map Prod.fst).Nodup) : VNode S E inv snap :=
  .keyed (xs.map Prod.fst) (KList.ofList xs) nodup

/-- A keyed list built by mapping over `xs` (`xs.map(x => <El key={key(x)}/>)`).
The node builder receives a membership proof, so obligations inside the body
may use facts about `x` that hold for all elements of `xs`. -/
def VNode.keyedMap {S E inv snap} {α : Type} (xs : List α) (key : α → Key)
    (node : (x : α) → x ∈ xs → VNode S E inv snap) (nodup : (xs.map key).Nodup) : VNode S E inv snap :=
  VNode.keyedOf (xs.attach.map (fun ⟨x, hx⟩ => (key x, node x hx))) (by
    have : (List.map Prod.fst (List.map (fun (p : {x // x ∈ xs}) => (key p.1, node p.1 p.2)) xs.attach))
        = xs.map key := by
      rw [List.map_map]
      conv => rhs; rw [← List.attach_map_subtype_val xs, List.map_map]
      rfl
    rw [this]; exact nodup)

/-- An element with a `key={k}` outside a list.  JavaScript evaluates `k` on every
render, so the term `k` (with its proof obligations) is kept; the model
reconciles by position and component identity, and a key change (React remounts:
fresh state, `init_inv`) is covered because both keeping and resetting the state
are verified. -/
def VNode.withKey {S E inv snap} {α : Type} (_k : α) (n : VNode S E inv snap) : VNode S E inv snap := n

/-- A boolean JSX child `{b}`: React renders nothing, but JavaScript evaluates `b`
(so its proof obligations are kept in the term). -/
def VNode.ofBool {S E inv snap} (_b : Bool) : VNode S E inv snap := .empty

/-- `xs.map(x => <El/>)` without keys is rejected by the translator (React
requires keys); `mapNodes` is used for non-element results such as text. -/
def VNode.mapList {S E inv snap} {α : Type} (xs : List α)
    (node : (x : α) → x ∈ xs → VNode S E inv snap) : VList S E inv snap :=
  VList.ofList (xs.attach.map (fun ⟨x, hx⟩ => node x hx))

/-- A component: a specification plus a proof-carrying render function. -/
structure Component (spec : Spec) : Type 1 where
  render : {E : Type} → (d : spec.D) → (cb : spec.Cb d E) → (s : spec.S) →
    spec.pre d → spec.inv d s → VNode spec.S E (spec.inv d) s

/-- `<C {...d} {...cb}/>` rendered by a parent. -/
def Component.node {S E inv snap} {spec : Spec} (c : Component spec) (d : spec.D)
    (cb : spec.Cb d (Emit S E inv snap)) (h : spec.pre d) : VNode S E inv snap :=
  .comp spec d cb h (fun s hs => c.render d cb s h hs)

/-! ## Smart constructors used by generated code -/

/-- Callbacks record for components without callback props. -/
structure NoCb (d : D) (E : Type) : Type where

@[simp] theorem nodup_map_key_int {α} (xs : List α) (f : α → Int) :
    (xs.map (fun x => Key.int (f x))).Nodup ↔ (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.nodup_cons, List.mem_map, Key.int.injEq, ih]
@[simp] theorem nodup_map_key_str {α} (xs : List α) (f : α → JS.Str) :
    (xs.map (fun x => Key.str (f x))).Nodup ↔ (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.nodup_cons, List.mem_map, Key.str.injEq, ih]

/-- `assume(c)` in VTS: a trusted fact.  Every declaration that relies on it lists
`VReact.assumed` in `#print axioms`, so `vreact verify` reports it as ASSUMES. -/
axiom assumed {p : Prop} : p

/-- Package a parent outcome for a child callback. -/
def Emit.mk {S E inv snap} (o : Outcome S E) (h : inv (o.apply snap)) : Emit S E inv snap := ⟨o, h⟩

/-- Package a parent outcome of a component with deferred updates: checked
`RebaseSafe` (React may rebase the parent's queued updates onto pending
lower-priority ones). -/
def Emit.rebased {S E X : Type} {inv : S → Prop} {snap : S} (o : Outcome S E) (vary : X → S) (x₀ : X)
    (hx : vary x₀ = snap) (hs : inv snap) (h : RebaseSafe inv vary o) : Emit S E inv snap :=
  ⟨o, RebaseSafe.at_snap x₀ hx hs h⟩

end VReact
