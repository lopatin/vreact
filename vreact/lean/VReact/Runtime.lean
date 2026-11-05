import VReact.Core
/-!
# VReact.Runtime — the React lifecycle as a transition system

This file gives an operational semantics to a running React application built
from `VReact.Component`s and proves the soundness theorem:

> **Theorem (`reachable_allInv`).** For every sequence of user events, async
> timer firings, effect flushes and prop changes, every mounted component
> instance satisfies its invariant.

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
* `flushEffects` — after commit, effects whose dependencies changed run; their
  updates are robust, so it is sound to run them in any order and any number of
  times (as React does in StrictMode).
* `fireTask` — an async callback (setInterval/setTimeout) registered by an
  effect fires; it closes over an *old* snapshot, hence robust updates.

Recursion through component trees is bounded by a `fuel` argument (React's own
maximum update depth); with insufficient fuel a subtree is not mounted, which is
safe for invariants (nothing unverified ever runs).

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

/-- After a commit: run the effects whose dependencies changed (all of them the
first time), replace the registered timers (cleanup + setup), re-render. -/
noncomputable def flushEffects (fuel : Nat) : {E : Type} → Inst E → Inst E
  | _, i@(.mk c s hinv deps tasks kids) =>
      let effs := (c.render s hinv).effectsOf
      let firing := effs.filter (fun eff => eff.fires (deps.map (fun _ => eff.deps)))
      if firing.isEmpty ∧ deps.isSome then i
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
  /-- React flushes passive effects of an instance after a commit -/
  | flush (inst : List Path)
  /-- an asynchronous callback registered by an effect fires -/
  | task (inst : List Path) (k : Nat) (e : DomEvent)

noncomputable def step (fuel : Nat) {E : Type} (i : Inst E) : Action → Inst E
  | .event inst el ev e => (dispatch fuel i inst el ev e).1
  | .flush inst => i.modifyAt (flushEffects fuel) inst
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
application, whatever timers fire and whenever React flushes effects, every
mounted component instance satisfies its invariant.

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

end VReact
