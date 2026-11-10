import VReact.Core
/-!
# VReact.Runtime — the React lifecycle as a transition system

This file gives an operational semantics to a running React application built
from `VReact.Component`s and proves the soundness theorem:

> **Theorem (`run_allInv`).** For every sequence of user events, async
> timer firings, effect flushes, remounts and prop changes, every mounted
> component instance satisfies its invariant.

## The runtime state

A mounted instance (`Inst E`) records the element that created it (`CompNode`:
the component's spec, data props, callbacks and render closure as provided by
the parent's latest render), its current hook state with the proof of its
invariant, the dependency values of its effects at the last flush, the
asynchronous callbacks (timers) its effects registered, and its mounted
children.  The type of a child's parent-callback results is
`Emit S E (inv d) s` — it mentions the parent's *current* state `s`, so a
child can only ever hand its parent outcomes that were proven safe against the
parent's current state (React flushes discrete events synchronously, so the
parent's snapshot is current).

## Transitions

* `mount` — run initialisers (`useState(init)`), render, mount children.
* `reconcile` — after a re-render, match new child elements against old
  instances *by position/key and component identity* (React's reconciliation):
  same component ⇒ keep the state (needs `Spec.stable`); otherwise mount fresh
  (needs `Spec.init_inv`).  Removed children are unmounted (dropped).
* `dispatch` — a discrete DOM event runs one handler of the latest render; its
  queued updates are processed (`Outcome.apply`), its parent callback (if any)
  is propagated to the parent, and every affected instance re-renders.
* `flushEffects` — after commit, the effects whose dependencies changed since the
  previous render run (React compares each dependency with `Object.is`; where the
  model's values do not decide it — objects, `number`s, an int zero that may be
  `-0` — the run chooses, `Action.flush`); at the first flush after mounting the
  run may choose to run every effect a second time, as React's StrictMode does in
  development (`flushRuns`).  Their updates are robust, so it is sound to run them
  in any order and any number of times.
* `Inst.remount` — React unmounts an instance and mounts its element afresh when
  its `key` outside a list, or the type of an enclosing host element, changes;
  the model's paths contain neither, so a run may remount any instance at any
  time (`Action.remount`): initial state, every effect runs at the next flush.
* `fireTask` — an async callback (setInterval/setTimeout) registered by an
  effect fires; it closes over an *old* snapshot, hence robust updates.

Recursion through component trees is bounded by a `fuel` argument, a bound on the
depth of the mount/reconcile walk; with insufficient fuel a subtree is not mounted,
which is safe for invariants (nothing unverified ever runs). It is not React's
nested-update limit ("Maximum update depth exceeded", which React throws from a setter
after 50 nested synchronous commits): the model's setters never throw, and VTS rejects
what makes such chains (a focus handler that updates state on or around an
`autoFocus` element, SEMANTICS §2.2).

The semantics is `noncomputable`: reconciliation decides component identity with
classical equality on specifications (React compares element types by identity).
-/
namespace VReact
open Classical

/-! ## Element positions -/

inductive PathSeg where
  | idx (n : Nat)
  | key (k : Key)
deriving DecidableEq, Repr

abbrev Path := List PathSeg

/-- A child element `<C …/>` as produced by a parent's render. -/
structure CompNode (E : Type) : Type 1 where
  spec : Spec
  d : spec.D
  cb : spec.Cb d E
  hpre : spec.pre d
  render : (s : spec.S) → spec.inv d s → VNode spec.S E (spec.inv d) s

mutual
/-- All child component elements of a rendered tree, with their positions. -/
def VNode.comps {S E : Type} {inv : S → Prop} {snap : S} :
    VNode S E inv snap → Path → List (Path × CompNode (Emit S E inv snap))
  | .empty, _ => []
  | .text _, _ => []
  | .elem _ _ _ kids, p => VList.comps kids p 0
  | .keyed _ items _, p => KList.comps items p
  | .comp spec d cb pre render, p => [(p, ⟨spec, d, cb, pre, render⟩)]
  | .withEffects _ body, p => VNode.comps body p
def VList.comps {S E : Type} {inv : S → Prop} {snap : S} :
    VList S E inv snap → Path → Nat → List (Path × CompNode (Emit S E inv snap))
  | .nil, _, _ => []
  | .cons h t, p, i => VNode.comps h (p ++ [.idx i]) ++ VList.comps t p (i + 1)
def KList.comps {S E : Type} {inv : S → Prop} {snap : S} {ks : List Key} :
    KList S E inv snap ks → Path → List (Path × CompNode (Emit S E inv snap))
  | .nil, _ => []
  | .cons k h t, p => VNode.comps h (p ++ [.key k]) ++ KList.comps t p
end

mutual
/-- The handler for event `ev` on the host element at `path`, if any. -/
def VNode.handlerAt {S E : Type} {inv : S → Prop} {snap : S} :
    VNode S E inv snap → Path → String → Option (Handler S E inv snap)
  | .elem _ _ hs _, [], ev => hs.find? (fun h => h.event == ev)
  | .elem _ _ _ kids, .idx i :: rest, ev => VList.handlerAt kids i rest ev
  | .keyed _ items _, .key k :: rest, ev => KList.handlerAt items k rest ev
  | .withEffects _ body, p, ev => VNode.handlerAt body p ev
  | _, _, _ => none
def VList.handlerAt {S E : Type} {inv : S → Prop} {snap : S} :
    VList S E inv snap → Nat → Path → String → Option (Handler S E inv snap)
  | .nil, _, _, _ => none
  | .cons h _, 0, p, ev => VNode.handlerAt h p ev
  | .cons _ t, n + 1, p, ev => VList.handlerAt t n p ev
def KList.handlerAt {S E : Type} {inv : S → Prop} {snap : S} {ks : List Key} :
    KList S E inv snap ks → Key → Path → String → Option (Handler S E inv snap)
  | .nil, _, _, _ => none
  | .cons k' h t, k, p, ev => if k' = k then VNode.handlerAt h p ev else KList.handlerAt t k p ev
end

/-- The effects declared by a component's render (attached at its root). -/
def VNode.effectsOf {S E : Type} {inv : S → Prop} {snap : S} : VNode S E inv snap → List (Effect S E inv)
  | .withEffects effs _ => effs
  | _ => []

/-! ## Mounted instances -/

/-- An asynchronous callback registered by an effect: a robust state update. -/
def Task (S : Type) (inv : S → Prop) : Type := { t : DomEvent → S → S // ∀ e s, inv s → inv (t e s) }

mutual
inductive Inst : Type → Type 1 where
  | mk {E : Type} (c : CompNode E) (s : c.spec.S) (hinv : c.spec.inv c.d s)
      (deps : Option (List (Option (List DepVal))))
      (tasks : List (Task c.spec.S (c.spec.inv c.d)))
      (children : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) : Inst E
inductive Insts : Type → Type 1 where
  | nil {E : Type} : Insts E
  | cons {E : Type} (p : Path) (i : Inst E) (rest : Insts E) : Insts E
end

/-- An instance of some (existentially packaged) parent-outcome type. -/
abbrev AnyInst : Type 1 := Σ E : Type, Inst E

def Insts.find {E : Type} : Insts E → Path → Option (Inst E)
  | .nil, _ => none
  | .cons p i rest, q => if p = q then some i else rest.find q

def Insts.toList {E : Type} : Insts E → List (Path × Inst E)
  | .nil => []
  | .cons p i rest => (p, i) :: rest.toList

def Insts.ofList {E : Type} : List (Path × Inst E) → Insts E
  | [] => .nil
  | (p, i) :: rest => .cons p i (Insts.ofList rest)

/-- Re-index old children by position so that they can be matched against new elements. -/
def Inst.oldChildren {E : Type} : Inst E → List (Path × AnyInst)
  | .mk _ _ _ _ _ kids => kids.toList.map (fun (p, i) => (p, ⟨_, i⟩))

/-- State carried over to a re-rendered element of the *same* component
(React keeps hook state); the invariant is re-established by `Spec.stable`. -/
noncomputable def keepState {spec₁ spec₂ : Spec} (h : spec₁ = spec₂) (d₁ : spec₁.D) (s₁ : spec₁.S)
    (h₁ : spec₁.inv d₁ s₁) (d₂ : spec₂.D) (hpre₂ : spec₂.pre d₂) : { s : spec₂.S // spec₂.inv d₂ s } := by
  subst h
  exact ⟨s₁, spec₁.stable d₁ d₂ s₁ h₁ hpre₂⟩

/-- Tasks registered under old props remain valid under new props: stability makes
the invariants for any two admissible props equivalent. -/
noncomputable def transportTasks {spec₁ spec₂ : Spec} (h : spec₁ = spec₂) (d₁ : spec₁.D) (hpre₁ : spec₁.pre d₁)
    (d₂ : spec₂.D) (hpre₂ : spec₂.pre d₂) (ts : List (Task spec₁.S (spec₁.inv d₁))) :
    List (Task spec₂.S (spec₂.inv d₂)) := by
  subst h
  exact ts.map (fun t => ⟨t.1, fun e s hs =>
    spec₁.stable d₁ d₂ _ (t.2 e s (spec₁.stable d₂ d₁ s hs hpre₁)) hpre₂⟩)

/-- What we know about an old instance at a position: its spec, props, state, tasks, children. -/
structure OldState where
  spec : Spec
  d : spec.D
  hpre : spec.pre d
  s : spec.S
  hinv : spec.inv d s
  deps : Option (List (Option (List DepVal)))
  tasks : List (Task spec.S (spec.inv d))
  kids : List (Path × AnyInst)

def AnyInst.old : AnyInst → OldState
  | ⟨_, .mk c s hinv deps tasks kids⟩ => ⟨c.spec, c.d, c.hpre, s, hinv, deps, tasks, kids.toList.map (fun (p, i) => (p, ⟨_, i⟩))⟩

/-! ## Mounting and reconciliation -/

mutual
/-- Mount element `c`, adopting the state of `old` when it is the same component. -/
noncomputable def mount (fuel : Nat) {E : Type} (c : CompNode E) (old : Option OldState) : Inst E :=
  -- choose the state: keep (same component type) or initialise
  let chosen : { s : c.spec.S // c.spec.inv c.d s } × Option (List (Option (List DepVal))) ×
      List (Task c.spec.S (c.spec.inv c.d)) × List (Path × AnyInst) :=
    match old with
    | some o =>
        if h : o.spec = c.spec then
          (keepState h o.d o.s o.hinv c.d c.hpre, o.deps, transportTasks h o.d o.hpre c.d c.hpre o.tasks, o.kids)
        else (⟨c.spec.init c.d c.hpre, c.spec.init_inv c.d c.hpre⟩, none, [], [])
    | none => (⟨c.spec.init c.d c.hpre, c.spec.init_inv c.d c.hpre⟩, none, [], [])
  let s := chosen.1.1
  let hinv := chosen.1.2
  let view := c.render s hinv
  .mk c s hinv chosen.2.1 chosen.2.2.1
    (match fuel with
     | 0 => .nil
     | f + 1 => reconcile f chosen.2.2.2 (view.comps []))

/-- Match the new child elements against the old instances by position. -/
noncomputable def reconcile (fuel : Nat) {E : Type} (old : List (Path × AnyInst)) :
    List (Path × CompNode E) → Insts E
  | [] => .nil
  | (p, c) :: rest =>
      .cons p (mount fuel c ((old.find? (fun x => x.1 = p)).map (fun x => x.2.old))) (reconcile fuel old rest)
end

/-- Re-render an instance after its state changed (keeps its element). -/
noncomputable def Inst.rerender (fuel : Nat) {E : Type} : Inst E → Inst E
  | i@(.mk c s hinv deps tasks _) =>
      .mk c s hinv deps tasks (reconcile fuel i.oldChildren ((c.render s hinv).comps []))

/-! ## Instance helpers -/

def Insts.replace {E : Type} : Insts E → Path → Inst E → Insts E
  | .nil, _, _ => .nil
  | .cons p i rest, q, j => if p = q then .cons p j rest else .cons p i (rest.replace q j)

def Insts.anyList {E : Type} (kids : Insts E) : List (Path × AnyInst) :=
  kids.toList.map (fun (p, i) => (p, ⟨_, i⟩))

/-- A handler offered by the render for snapshot `snap` is safe to run when the
current state is `snap` (discrete) — and, being robust, also when it is not
(continuous). -/
theorem Handler.ok_at {S E : Type} {inv : S → Prop} {snap : S} (h : Handler S E inv snap) (e : DomEvent)
    (hs : inv snap) : inv ((h.run e).apply snap) := by
  cases h with
  | discrete ev run ok _ => exact ok e
  | continuous ev run ok _ => exact ok e snap hs

/-! ## Event dispatch

`dispatch fuel i instPath elPath ev e` delivers DOM event `ev` to the host
element at `elPath` inside the instance reached by `instPath`.  It returns the
new instance and, if the handler (or a descendant's callback chain) invoked a
callback of *this* instance's parent, the parent outcome to apply next.  The
type of that outcome (`E`) carries its proof of safety. -/
noncomputable def dispatch (fuel : Nat) : {E : Type} → Inst E → List Path → Path → String → DomEvent → Inst E × Option E
  | _, i@(.mk c s hinv deps tasks kids), [], el, ev, e =>
      match (c.render s hinv).handlerAt el ev with
      | none => (i, none)
      | some h =>
          let o := h.run e
          let hok : c.spec.inv c.d (o.apply s) := h.ok_at e hinv
          (.mk c (o.apply s) hok deps tasks (reconcile fuel kids.anyList ((c.render (o.apply s) hok).comps [])), o.emit)
  | _, i@(.mk c s hinv deps tasks kids), p :: rest, el, ev, e =>
      match kids.find p with
      | none => (i, none)
      | some child =>
          let r := dispatch fuel child rest el ev e
          let kids' := kids.replace p r.1
          match r.2 with
          | none => (.mk c s hinv deps tasks kids', none)
          | some em =>
              -- the child invoked one of our callbacks: `em` is our outcome, proven safe for our state
              (.mk c (em.1.apply s) em.2 deps tasks
                 (reconcile fuel kids'.anyList ((c.render (em.1.apply s) em.2).comps [])), em.1.emit)

/-! ## Effects and asynchronous callbacks -/

/-- Run a list of robust outcomes in sequence. -/
def runRobust {S E : Type} {inv : S → Prop} : List (Effect S E inv) → { s : S // inv s } → { s : S // inv s }
  | [], st => st
  | eff :: rest, ⟨s, h⟩ => runRobust rest ⟨eff.setup.apply s, eff.setup_ok s h⟩

/-- The timers registered by an effect, as tasks. -/
def Effect.toTasks {S E : Type} {inv : S → Prop} (eff : Effect S E inv) : List (Task S inv) :=
  eff.tasks.attach.map (fun ⟨t, ht⟩ => ⟨fun e s => (t e).apply s, fun e s hs => (eff.tasks_ok t ht e).1 s hs⟩)

/-- An effect registers one task per timer. -/
@[simp] theorem Effect.toTasks_length {S E : Type} {inv : S → Prop} (eff : Effect S E inv) :
    eff.toTasks.length = eff.tasks.length :=
  (List.length_map _).trans List.length_attach

/-- The dependency array that the previous render gave effect number `k` of an
instance whose recorded dependencies are `deps` (`none`: the first commit after
mounting — React keeps one effect per hook, so a missing entry is one too). -/
def prevDeps (deps : Option (List (Option (List DepVal)))) (k : Nat) : Option (Option (List DepVal)) :=
  deps.bind (·[k]?)

/-- The effects of a render that run after its commit, numbered from `k`: each one is
compared with the dependency array the *previous* render gave the effect at the same
position (`prevDeps`; React 18 `updateEffectImpl` compares with the deps stored in the
current hook).  `rerun k` decides effect `k` when the model's values leave `Object.is`
open (`Effect.fires`, `depsChanged`). -/
def firingFrom {S E : Type} {inv : S → Prop} (deps : Option (List (Option (List DepVal))))
    (rerun : Nat → Bool) : Nat → List (Effect S E inv) → List (Effect S E inv)
  | _, [] => []
  | k, eff :: rest =>
      if eff.fires (prevDeps deps k) (rerun k) then eff :: firingFrom deps rerun (k + 1) rest
      else firingFrom deps rerun (k + 1) rest

/-- The effects a flush runs, in order: those `firingFrom` selects and, at the first
flush after mounting (`deps = none`, where every effect is selected: `firingFrom_none`)
when the run chooses `strict`, every effect a second time.  That is React 18's
StrictMode in development: after the commit that mounted a component,
`commitDoubleInvokeEffectsInDEV` runs the cleanup and then the setup of each of its
effects again, in the same flush and with the same render's closures, so the updates
of the second setups queue after those of the first. -/
def flushRuns {S E : Type} {inv : S → Prop} (deps : Option (List (Option (List DepVal))))
    (rerun : Nat → Bool) (strict : Bool) (effs : List (Effect S E inv)) : List (Effect S E inv) :=
  firingFrom deps rerun 0 effs ++ (if strict && deps.isNone then effs else [])

/-- After a commit: run the effects whose dependencies changed since the previous
render (all of them the first time, twice when the run chooses StrictMode's double
invocation: `flushRuns`), register their timers, record this render's dependencies
(React stores them whether or not the effect ran), and re-render when an effect
ran.  The model has no cleanup step: the timers of earlier runs stay registered, so
a run may still fire a timer React cleared (more runs, not fewer). -/
noncomputable def flushEffects (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) : {E : Type} → Inst E → Inst E
  | _, .mk c s hinv deps tasks kids =>
      let effs := (c.render s hinv).effectsOf
      let firing := flushRuns deps rerun strict effs
      if firing.isEmpty then .mk c s hinv (some (effs.map (·.deps))) tasks kids
      else
        let r := runRobust firing ⟨s, hinv⟩
        let tasks' := firing.flatMap Effect.toTasks ++ tasks
        .mk c r.1 r.2 (some (effs.map (·.deps))) tasks'
          (reconcile fuel kids.anyList ((c.render r.1 r.2).comps []))

/-- An asynchronous callback (timer) fires against the *current* state. -/
noncomputable def fireTask (fuel : Nat) (k : Nat) (e : DomEvent) : {E : Type} → Inst E → Inst E
  | _, i@(.mk c s hinv deps tasks kids) =>
      match tasks[k]? with
      | none => i
      | some t =>
          let s' := t.1 e s
          .mk c s' (t.2 e s hinv) deps tasks (reconcile fuel kids.anyList ((c.render s' (t.2 e s hinv)).comps []))

/-- A remount: React unmounts the instance (its timers can no longer change any state:
a setter of an unmounted component does nothing) and mounts its element afresh —
initial state (`init_inv`), no recorded dependencies (so the next flush runs every
effect), no timers, children mounted afresh.  React does it when the element's `key`
outside a list changes, or the type of an enclosing host element (`<div>` →
`<section>`, a Fragment ↔ an element); the model's paths contain neither, so
`reconcile` keeps the instance there, and a run may remount any instance at any time
instead (`Action.remount`: more runs, not fewer). -/
noncomputable def Inst.remount (fuel : Nat) : {E : Type} → Inst E → Inst E
  | _, .mk c _ _ _ _ _ => mount fuel c none

/-- Apply `f` to the instance at an instance path. -/
noncomputable def Inst.modifyAt (f : {E : Type} → Inst E → Inst E) : {E : Type} → Inst E → List Path → Inst E
  | _, i, [] => f i
  | _, i@(.mk c s hinv deps tasks kids), p :: rest =>
      match kids.find p with
      | none => i
      | some child => .mk c s hinv deps tasks (kids.replace p (Inst.modifyAt f child rest))

/-! ## Runs -/

/-- Everything that can happen to a mounted application. -/
inductive Action where
  /-- the user interacts with a host element -/
  | event (inst : List Path) (el : Path) (ev : String) (e : DomEvent)
  /-- React flushes passive effects of an instance after a commit; `rerun k` is whether
  React re-runs effect number `k` where the model's dependency values do not decide
  `Object.is` (objects, `number`s, an int 0 that may be `-0`: `DepVal.same`); `strict`
  is whether, at the first flush after mounting, every effect runs a second time
  (StrictMode in development: `flushRuns`) -/
  | flush (inst : List Path) (rerun : Nat → Bool) (strict : Bool)
  /-- React remounts an instance (a changed `key` outside a list, a changed enclosing
  host element type: `Inst.remount`) -/
  | remount (inst : List Path)
  /-- an asynchronous callback registered by an effect fires -/
  | task (inst : List Path) (k : Nat) (e : DomEvent)

noncomputable def step (fuel : Nat) {E : Type} (i : Inst E) : Action → Inst E
  | .event inst el ev e => (dispatch fuel i inst el ev e).1
  | .flush inst rerun strict => i.modifyAt (flushEffects fuel rerun strict) inst
  | .remount inst => i.modifyAt (Inst.remount fuel) inst
  | .task inst k e => i.modifyAt (fireTask fuel k e) inst

/-- The root element (e.g. `<App/>` passed to `createRoot(…).render`). -/
noncomputable def start (fuel : Nat) (root : CompNode Empty) : Inst Empty := mount fuel root none

/-- The application after a sequence of actions. -/
noncomputable def run (fuel : Nat) (root : CompNode Empty) (acts : List Action) : Inst Empty :=
  acts.foldl (step fuel) (start fuel root)

/-! ## Soundness -/

mutual
/-- Every instance of the tree satisfies its component's invariant for its current props. -/
def Inst.AllInv : {E : Type} → Inst E → Prop
  | _, .mk c s _ _ _ kids => c.spec.inv c.d s ∧ Insts.AllInv kids
def Insts.AllInv : {E : Type} → Insts E → Prop
  | _, .nil => True
  | _, .cons _ i rest => Inst.AllInv i ∧ Insts.AllInv rest
end

mutual
theorem Inst.allInv : {E : Type} → (i : Inst E) → i.AllInv
  | _, .mk c s hinv _ _ kids => ⟨hinv, Insts.allInv kids⟩
theorem Insts.allInv : {E : Type} → (k : Insts E) → k.AllInv
  | _, .nil => trivial
  | _, .cons _ i rest => ⟨Inst.allInv i, Insts.allInv rest⟩
end

/-- **Soundness of verified components.**  However the user interacts with the
application, whatever timers fire, whenever React flushes effects (StrictMode's
second run at mount included) and whichever instances it remounts, every mounted
component instance satisfies its invariant.

The proof is by construction: `dispatch`, `flushEffects`, `fireTask` and
`reconcile` can only be *defined* because each component supplies its proof
obligations (handler safety, robust effects, `init_inv`, `stable`, child
preconditions, callback contracts) — those are exactly the obligations that
`vreact verify` discharges for every component. -/
theorem run_allInv (fuel : Nat) (root : CompNode Empty) (acts : List Action) :
    (run fuel root acts).AllInv :=
  Inst.allInv _

/-! ## Facts about the update-queue model (React batching semantics) -/

/-- `setX(v); setX(v)` — two replace-updates computed from the same snapshot —
has the effect of a single one (React batches; the second does not see the first). -/
theorem replace_twice {S E : Type} (u : S → S) (hidem : ∀ s, u (u s) = u s) (s : S) (e : Option E) :
    (Outcome.mk [u, u] e).apply s = (Outcome.mk [u] e).apply s := by
  simp [Outcome.apply, hidem]

/-- Functional updates compose: `setN(n => n + 1)` twice adds two. -/
theorem functional_twice (n : Int) (e : Option Empty) :
    (Outcome.mk [fun (m : Int) => m + 1, fun m => m + 1] e).apply n = n + 2 := by
  simp [Outcome.apply]; omega

/-- A replace update computed from the snapshot ignores intermediate updates:
`setN(snap + 1)` after `setN(m => m + 5)` still yields `snap + 1`. -/
theorem replace_after_functional (snap : Int) (e : Option Empty) :
    (Outcome.mk [fun (m : Int) => m + 5, fun _ => snap + 1] e).apply snap = snap + 1 := by
  simp [Outcome.apply]

/-- Rebasing is safe (React 18 lanes, SEMANTICS §2.2).  A deferred outcome `u`
(timer, effect, continuous/default-priority handler: robust, writing only the
deferred fields) is pending when a discrete outcome `f`, checked `RebaseSafe`
against its snapshot `vary x₀`, is queued.  React may render `f` alone (skipping
`u`), `u` alone, and finally `f` re-applied on top of `u`; all three keep the
invariant.  `dispatch`/`fireTask` above model the in-order case. -/
theorem rebase_safe {S E X : Type} {inv : S → Prop} (vary : X → S) (x₀ : X)
    (u f : Outcome S E) (hu : Robust inv u) (hu' : ∀ x, ∃ x', u.apply (vary x) = vary x')
    (hf : RebaseSafe inv vary f) (h₀ : inv (vary x₀)) :
    inv (f.apply (vary x₀)) ∧ inv (u.apply (vary x₀)) ∧ inv (f.apply (u.apply (vary x₀))) := by
  obtain ⟨x', hx'⟩ := hu' x₀
  have h1 := hu _ h₀
  refine ⟨hf x₀ h₀, h1, ?_⟩
  rw [hx'] at h1 ⊢
  exact hf x' h1

/-- The component and state of an instance. -/
def Inst.stateSigma {E : Type} : Inst E → Σ spec : Spec, spec.S
  | .mk c s .. => ⟨c.spec, s⟩

theorem keepState_val {spec₁ spec₂ : Spec} (h : spec₁ = spec₂) (d₁ : spec₁.D) (s₁ : spec₁.S)
    (h₁ : spec₁.inv d₁ s₁) (d₂ : spec₂.D) (hpre₂ : spec₂.pre d₂) :
    (⟨spec₂, (keepState h d₁ s₁ h₁ d₂ hpre₂).1⟩ : Σ spec : Spec, spec.S) = ⟨spec₁, s₁⟩ := by
  subst h; rfl

/-- React keeps the state of an element of the same component at the same
position: re-mounting over an old instance of the same component adopts its
state unchanged. -/
theorem mount_keeps_state (fuel : Nat) {E : Type} (c : CompNode E) (o : OldState) (h : o.spec = c.spec) :
    (mount fuel c (some o)).stateSigma = ⟨o.spec, o.s⟩ := by
  cases fuel <;> simp only [mount, h, dite_true, Inst.stateSigma] <;> exact keepState_val h _ _ _ _ _

/-- …and a different component at that position starts from its initial state. -/
theorem mount_fresh_state (fuel : Nat) {E : Type} (c : CompNode E) (o : OldState) (h : o.spec ≠ c.spec) :
    (mount fuel c (some o)).stateSigma = ⟨c.spec, c.spec.init c.d c.hpre⟩ := by
  cases fuel <;> simp [mount, h, Inst.stateSigma]

/-! ## Facts about effect re-runs (React 18 `updateEffectImpl`, `areHookInputsEqual`) -/

-- a dependency that changed value re-runs the effect, whatever the run chooses
example : depsChanged [.int 1] [.int 2] false = true := by decide
example : depsChanged [.bool true, .int 7] [.bool false, .int 7] false = true := by decide
-- equal values do not, whatever the run chooses
example : depsChanged [.int 7, .bool true] [.int 7, .bool true] true = false := by decide
example : depsChanged [] [] true = false := by decide
-- `0` may have become `-0` (or not): the run decides
example : depsChanged [.int 0] [.int 0] true = true := by decide
example : depsChanged [.int 0] [.int 0] false = false := by decide
-- an object's identity is not modelled: the run decides, unless another dependency changed
example : depsChanged [.obj, .int 1] [.obj, .int 1] true = true := by decide
example : depsChanged [.obj, .int 1] [.obj, .int 1] false = false := by decide
example : depsChanged [.obj, .int 1] [.obj, .int 2] false = true := by decide

/-- The stored dependency arrays of an instance. -/
def Inst.depsOf {E : Type} : Inst E → Option (List (Option (List DepVal)))
  | .mk _ _ _ deps _ _ => deps

/-- The number of timers (tasks) an instance has registered. -/
def Inst.timerCount {E : Type} : Inst E → Nat
  | .mk _ _ _ _ tasks _ => tasks.length

/-- A flush records the dependency arrays of the current render, as React stores
each render's dependencies, whether or not the effect ran. -/
theorem flushEffects_depsOf (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) {E : Type} (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (deps : Option (List (Option (List DepVal))))
    (tasks : List (Task c.spec.S (c.spec.inv c.d))) (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) :
    (flushEffects fuel rerun strict (.mk c s hinv deps tasks kids)).depsOf
      = some ((c.render s hinv).effectsOf.map (·.deps)) := by
  simp only [flushEffects]
  split <;> rfl

/-- Effect number `j` is compared with the dependency array recorded for effect number `j`
(and decided by `rerun j`): a flush runs, in order, exactly the effects whose own
dependencies changed. -/
theorem firingFrom_eq {S E : Type} {inv : S → Prop} (deps : Option (List (Option (List DepVal))))
    (rerun : Nat → Bool) : ∀ (k : Nat) (effs : List (Effect S E inv)),
    firingFrom deps rerun k effs
      = ((List.range' k effs.length).zip effs).filterMap
          (fun p => if p.2.fires (prevDeps deps p.1) (rerun p.1) then some p.2 else none)
  | _, [] => rfl
  | k, eff :: rest => by
      rw [firingFrom, List.length_cons, List.range'_succ, List.zip_cons_cons, List.filterMap_cons,
        firingFrom_eq deps rerun (k + 1) rest]
      split <;> simp_all

/-- Two effects whose dependencies change independently: each is compared with its own
recorded array (a flush that compared every effect with the first one's would run the
second effect here too). -/
theorem firingFrom_two {S E : Type} {inv : S → Prop} (rerun : Nat → Bool) (e₀ e₁ : Effect S E inv)
    (old₀ old₁ new₀ new₁ : List DepVal) (h₀ : e₀.deps = some new₀) (h₁ : e₁.deps = some new₁) :
    firingFrom (some [some old₀, some old₁]) rerun 0 [e₀, e₁]
      = (if depsChanged old₀ new₀ (rerun 0) then [e₀] else [])
          ++ (if depsChanged old₁ new₁ (rerun 1) then [e₁] else []) := by
  simp only [firingFrom, prevDeps, Effect.fires, h₀, h₁, Option.bind_some]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
  split <;> split <;> simp

/-- At the first flush after mounting every effect is selected. -/
theorem firingFrom_none {S E : Type} {inv : S → Prop} (rerun : Nat → Bool) :
    ∀ (k : Nat) (effs : List (Effect S E inv)), firingFrom none rerun k effs = effs
  | _, [] => rfl
  | k, eff :: rest => by simp [firingFrom, prevDeps, Effect.fires, firingFrom_none rerun (k + 1) rest]

/-- The first flush after mounting runs every effect — and every effect a second time
when the run chooses StrictMode's double invocation (`strict`). -/
theorem flushRuns_none {S E : Type} {inv : S → Prop} (rerun : Nat → Bool) (strict : Bool)
    (effs : List (Effect S E inv)) :
    flushRuns none rerun strict effs = if strict then effs ++ effs else effs := by
  cases strict <;> simp [flushRuns, firingFrom_none]

/-- After the first flush, `strict` changes nothing: React double-invokes effects only
at mount. -/
theorem flushRuns_some {S E : Type} {inv : S → Prop} (deps : List (Option (List DepVal)))
    (rerun : Nat → Bool) (strict : Bool) (effs : List (Effect S E inv)) :
    flushRuns (some deps) rerun strict effs = firingFrom (some deps) rerun 0 effs := by
  simp [flushRuns]

-- two concrete effects, deps `[a]` and `[b]`: `a` changed 1 → 2, `b` stayed 5; only the first runs
private def depEff (d : List DepVal) : Effect Unit Empty (fun _ => True) :=
  { deps := some d, setup := ⟨[], none⟩, setup_ok := fun _ _ => trivial, setup_noEmit := rfl,
    tasks := [], tasks_ok := by simp }
example : (firingFrom (some [some [.int 1], some [.int 5]]) (fun _ => true) 0
    [depEff [.int 2], depEff [.int 5]]).map (·.deps) = [some [.int 2]] := by decide
example : (firingFrom (some [some [.int 2], some [.int 4]]) (fun _ => true) 0
    [depEff [.int 2], depEff [.int 5]]).map (·.deps) = [some [.int 5]] := by decide
example : (firingFrom (some [some [.int 2], some [.int 5]]) (fun _ => true) 0
    [depEff [.int 2], depEff [.int 5]]).length = 0 := by decide
-- the undecided comparison of effect 1 is decided by `rerun 1`, not `rerun 0`
example : (firingFrom (some [some [.int 2], some [.obj]]) (fun k => k == 1) 0
    [depEff [.int 2], depEff [.obj]]).map (·.deps) = [some [.obj]] := by decide
example : (firingFrom (some [some [.obj], some [.int 5]]) (fun k => k == 1) 0
    [depEff [.obj], depEff [.int 5]]).length = 0 := by decide
-- at mount every effect runs, twice under StrictMode
example : (flushRuns none (fun _ => false) true [depEff [.int 2], depEff [.int 5]]).length = 4 := by decide
example : (flushRuns (some [some [.int 2], some [.int 5]]) (fun _ => false) true
    [depEff [.int 2], depEff [.int 5]]).length = 0 := by decide

/-- An effect runs again when a dependency changed since the previous render
(`depsChanged` against the array recorded at the last flush), and registers its
timers: the effect of a one-effect component, here.  (Before, the model compared
the effect's dependencies with themselves, so an effect with a dependency array
never ran a second time.) -/
theorem flushEffects_reruns (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) {E : Type} (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (old new : List DepVal)
    (tasks : List (Task c.spec.S (c.spec.inv c.d))) (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s))
    (eff : Effect c.spec.S E (c.spec.inv c.d)) (heffs : (c.render s hinv).effectsOf = [eff])
    (hnew : eff.deps = some new) (hch : depsChanged old new (rerun 0) = true) :
    (flushEffects fuel rerun strict (.mk c s hinv (some [some old]) tasks kids)).stateSigma
        = ⟨c.spec, eff.setup.apply s⟩ ∧
      (flushEffects fuel rerun strict (.mk c s hinv (some [some old]) tasks kids)).timerCount
        = eff.tasks.length + tasks.length := by
  simp [flushEffects, flushRuns, heffs, firingFrom, prevDeps, Effect.fires, hnew, hch, runRobust,
    Inst.stateSigma, Inst.timerCount]

/-- …and does not when no dependency changed: the instance keeps its state, timers
and children. -/
theorem flushEffects_keeps (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) {E : Type} (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s) (old new : List DepVal)
    (tasks : List (Task c.spec.S (c.spec.inv c.d))) (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s))
    (eff : Effect c.spec.S E (c.spec.inv c.d)) (heffs : (c.render s hinv).effectsOf = [eff])
    (hnew : eff.deps = some new) (hch : depsChanged old new (rerun 0) = false) :
    flushEffects fuel rerun strict (.mk c s hinv (some [some old]) tasks kids)
      = .mk c s hinv (some [some new]) tasks kids := by
  simp [flushEffects, flushRuns, heffs, firingFrom, prevDeps, Effect.fires, hnew, hch]

/-- With two effects, a flush runs exactly those whose own dependency array changed:
effect 0 alone when its dependencies changed and effect 1's did not. -/
theorem flushEffects_first_of_two (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) {E : Type}
    (c : CompNode E) (s : c.spec.S) (hinv : c.spec.inv c.d s) (old₀ old₁ new₀ new₁ : List DepVal)
    (tasks : List (Task c.spec.S (c.spec.inv c.d))) (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s))
    (e₀ e₁ : Effect c.spec.S E (c.spec.inv c.d)) (heffs : (c.render s hinv).effectsOf = [e₀, e₁])
    (h₀ : e₀.deps = some new₀) (h₁ : e₁.deps = some new₁)
    (hch₀ : depsChanged old₀ new₀ (rerun 0) = true) (hch₁ : depsChanged old₁ new₁ (rerun 1) = false) :
    (flushEffects fuel rerun strict (.mk c s hinv (some [some old₀, some old₁]) tasks kids)).stateSigma
        = ⟨c.spec, e₀.setup.apply s⟩ ∧
      (flushEffects fuel rerun strict (.mk c s hinv (some [some old₀, some old₁]) tasks kids)).timerCount
        = e₀.tasks.length + tasks.length := by
  simp [flushEffects, flushRuns, heffs, firingFrom_two rerun e₀ e₁ old₀ old₁ new₀ new₁ h₀ h₁, hch₀, hch₁,
    runRobust, Inst.stateSigma, Inst.timerCount]

/-- The first flush after mounting runs the effect of a one-effect component — twice when
the run chooses StrictMode's double invocation, with the same closure (React 18:
setup, cleanup, setup; the timers of the first setup stay registered in the model) —
and records its dependencies. -/
theorem flushEffects_mount (fuel : Nat) (rerun : Nat → Bool) (strict : Bool) {E : Type} (c : CompNode E)
    (s : c.spec.S) (hinv : c.spec.inv c.d s)
    (tasks : List (Task c.spec.S (c.spec.inv c.d))) (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s))
    (eff : Effect c.spec.S E (c.spec.inv c.d)) (heffs : (c.render s hinv).effectsOf = [eff]) :
    (flushEffects fuel rerun strict (.mk c s hinv none tasks kids)).stateSigma
        = ⟨c.spec, if strict then eff.setup.apply (eff.setup.apply s) else eff.setup.apply s⟩ ∧
      (flushEffects fuel rerun strict (.mk c s hinv none tasks kids)).timerCount
        = (if strict then 2 else 1) * eff.tasks.length + tasks.length ∧
      (flushEffects fuel rerun strict (.mk c s hinv none tasks kids)).depsOf = some [eff.deps] := by
  cases strict <;>
    simp [flushEffects, flushRuns, heffs, firingFrom, prevDeps, Effect.fires, runRobust, Inst.stateSigma,
      Inst.timerCount, Inst.depsOf] <;> omega

/-- Mounting an element afresh (at the start of a run, or where no instance of the same
component was): its initial state, no recorded dependencies (so the first flush runs every
effect: `flushEffects_mount`) and no timers. -/
theorem mount_none (fuel : Nat) {E : Type} (c : CompNode E) :
    ∃ kids, mount fuel c none = .mk c (c.spec.init c.d c.hpre) (c.spec.init_inv c.d c.hpre) none [] kids := by
  cases fuel <;> (rw [mount]; exact ⟨_, rfl⟩)

/-- A remount starts the instance afresh, from its current element. -/
theorem remount_eq (fuel : Nat) {E : Type} (c : CompNode E) (s : c.spec.S) (hinv : c.spec.inv c.d s)
    (deps : Option (List (Option (List DepVal)))) (tasks : List (Task c.spec.S (c.spec.inv c.d)))
    (kids : Insts (Emit c.spec.S E (c.spec.inv c.d) s)) :
    ∃ kids', Inst.remount fuel (.mk c s hinv deps tasks kids)
      = .mk c (c.spec.init c.d c.hpre) (c.spec.init_inv c.d c.hpre) none [] kids' :=
  mount_none fuel c

end VReact
