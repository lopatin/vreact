import VReact.JSMap
import VReact.Tactic
import VReact.Budget
import VReact.SelfTest
/-! Regression tests of the automation on `JSMap`/`JSSet` goals (the shapes the translation of
VTS Map/Set code produces), built with the library: a regression is a build error. -/
set_option linter.unusedVariables false
namespace VReact.JSMapTest.T1
open VReact VReact.JS
-- 1 get after set
example (m : JSMap Int Int) (k v : Int) : (m.set k v).get k = some v := by vreact_auto
-- 2 has after delete
example (m : JSMap Int Int) (k : Int) : (m.delete k).has k = false := by vreact_auto
-- 3 size after set
example (m : JSMap Int Int) (k v : Int) (h : m.has k = false) : (m.set k v).size = m.size + 1 := by vreact_auto
example (m : JSMap Int Int) (k v : Int) : m.size ≤ (m.set k v).size ∧ (m.set k v).size ≤ m.size + 1 := by vreact_auto
-- 4 key membership
example (m : JSMap Int Int) (k k' v : Int) (h : m.has k' = true) : (m.set k v).has k' = true := by vreact_auto
-- 5 every over values after set
example (m : JSMap Int Int) (k v : Int) (h : m.values.all (fun x => JS.le 0 x) = true) (hv : JS.le 0 v = true) :
    (m.set k v).values.all (fun x => JS.le 0 x) = true := by vreact_auto
-- 6 distinct keys / keyed rendering
example (m : JSMap Int Int) (k v : Int) : (m.set k v).keys.Nodup := by vreact_auto
example (m : JSMap Int JS.Str) : (m.entries.map (fun p => Key.int p.1)).Nodup := by vreact_auto
example (m : JSMap Int JS.Str) (k : Int) (v : JS.Str) : ((m.set k v).entries.map (fun p => Key.int p.1)).Nodup := by vreact_auto
-- 7 frame
example (m : JSMap Int Int) (k v : Int) : ∀ k', k' ≠ k → (m.set k v).get k' = m.get k' := by vreact_auto
-- 8 delete
example (m : JSMap Int Int) (k : Int) : (m.delete k).get k = none := by vreact_auto
example (m : JSMap Int Int) (k : Int) : Option.isNone ((m.delete k).get k) = true := by vreact_auto
-- 9 keepsHolds
example (m : JSMap Int Int) (id price : Int) :
    m.entries.all (fun p => JS.eq p.1 id || JS.eq ((m.set id price).get p.1) (some p.2)) = true := by vreact_auto
-- 10 literal maps
example : (JSMap.ofList [((1 : Int), (10 : Int)), (2, 20)]).get 2 = some 20 := by vreact_auto
example : (JSMap.ofList [((1 : Int), (10 : Int)), (1, 20)]).size = 1 := by vreact_auto
example : (JSMap.ofList [(JS.Str.ofString "a", (10 : Int)), (JS.Str.ofString "b", 20)]).get (JS.Str.ofString "b") = some 20 := by vreact_auto
-- 11 exact order (keys_set not in simp set: needs explicit lemma)
example (a b c : Int) : ((((JSMap.empty : JSMap Int Int).set 1 a).set 2 b).set 1 c).keys = [1, 2] := by
  simp only [JSMap.keys_set, JSMap.keys_empty]; decide
-- 12 polymorphic
example {K V : Type} [DecidableEq K] (m : JSMap K V) (k : K) (v : V) : (m.set k v).get k = some v ∧ (m.delete k).has k = false := by vreact_auto
example {K V : Type} [DecidableEq K] (P : V → Bool) (m : JSMap K V) (k : K) (v : V)
    (h : m.values.all P = true) (hv : P v = true) : ((m.set k v).delete k).values.all P = true ∧ (m.set k v).values.all P = true := by vreact_auto
example {K V : Type} [DecidableEq K] (m : JSMap K V) (k : K) (v : V) (h : m.get k = some v) : m.has k = true := by vreact_auto
-- 13 get after set of another key, then lookup known
example (m : JSMap Int Int) (a b : Int) (hab : a ≠ b) (h : m.get a = some 5) : ((m.set b 7).get a) = some 5 := by vreact_auto
-- 14 getD / match
example (m : JSMap Int Int) (k : Int) (h : m.values.all (fun x => JS.le 0 x) = true) : 0 ≤ (m.get k).getD 0 := by vreact_auto
example (m : JSMap Int Int) (k : Int) (h : m.values.all (fun x => JS.le 0 x) = true) :
    (match m.get k with | some x => 0 ≤ x | none => True) := by vreact_auto
-- Set
example (s : JSSet Int) (x : Int) : (s.add x).has x = true ∧ (s.delete x).has x = false := by vreact_auto
example (s : JSSet Int) (x : Int) (h : s.has x = false) : (s.add x).size = s.size + 1 := by vreact_auto
example (s : JSSet Int) (x : Int) (h : s.has x = true) : (s.delete x).size = s.size - 1 := by vreact_auto
example (s : JSSet Int) (x : Int) : ((if s.has x then s.delete x else s.add x).has x) = !(s.has x) := by vreact_auto
example (s : JSSet Int) (x : Int) : ((s.add x).elems.map Key.int).Nodup := by vreact_auto
example : (JSSet.ofList [(1 : Int), 2, 1]).size = 2 := by vreact_auto
example {T : Type} [DecidableEq T] (s : JSSet T) (x y : T) (h : x ≠ y) : (s.add x).has y = s.has y := by vreact_auto
end VReact.JSMapTest.T1
namespace VReact.JSMapTest.T2
open VReact VReact.JS
structure Ui where
  held : JSMap Int Int
  collapsed : JSSet Int
  heat : Int
@[vreact_simp] def wf (u : Ui) : Prop := 1 ≤ u.heat ∧ u.held.values.all (fun p => JS.le 0 p) = true ∧ (u.collapsed.size ≤ 10)
example (u : Ui) (id price : Int) (h : wf u) (hp : JS.le 0 price = true) : wf { u with held := u.held.set id price } := by vreact_auto
example (u : Ui) (id price : Int) : ({ u with held := u.held.set id price }).held.get id = some price := by vreact_auto
example (u : Ui) (id price : Int) : u.held.entries.all (fun h => JS.eq h.1 id || JS.eq (({ u with held := u.held.set id price }).held.get h.1) (some h.2)) = true := by vreact_auto
example (u : Ui) (id : Int) : let r := (if u.collapsed.has id then { u with collapsed := u.collapsed.delete id } else { u with collapsed := u.collapsed.add id }); JS.eq (r.collapsed.has id) (!(u.collapsed.has id)) = true := by vreact_auto
example (u : Ui) (id : Int) (h : wf u) : wf (if u.collapsed.has id then { u with collapsed := u.collapsed.delete id } else if JS.lt u.collapsed.size 10 then { u with collapsed := u.collapsed.add id } else u) := by vreact_auto
example (m : JSMap Int Int) (a b : Int) : ((m.set a 1).set b 2).get a = if a = b then some 2 else some 1 := by vreact_auto
example (m : JSMap Int Int) (cmp : Int → Int → Int) : ((JS.toSorted m.keys cmp).map Key.int).Nodup := by vreact_auto
example (m : JSMap Int Int) (k : Int) : ((m.delete k).keys.filter (fun x => JS.lt 0 x)).length ≤ m.keys.length := by vreact_auto
example (m : JSMap Int Int) (k : Int) (h : m.has k = true) : (m.delete k).size + 1 = m.size := by vreact_auto
example {T : Type} (id : T → Int) (m : JSMap Int T) (x : T) (h : ∀ k v, m.get k = some v → id v = k) :
    ∀ k v, (m.set (id x) x).get k = some v → id v = k := by vreact_auto
example {T : Type} (id : T → Int) (xs : List T) (x : T) (h : x ∈ xs) :
    (JSMap.ofList (xs.map (fun y => (id y, y)))).has (id x) = true := by vreact_auto
example {T : Type} (id : T → Int) (xs : List T) (x : T) (hn : (xs.map id).Nodup) (h : x ∈ xs) :
    (JSMap.ofList (xs.map (fun y => (id y, y)))).get (id x) = some x := by
  vreact_auto
-- whole-outcome shape
example (u : Ui) (h : wf u) (id price : Int) (hp : JS.le 0 price = true) :
    wf ((Outcome.mk (E := Empty) [fun t => { t with held := u.held.set id price }] none).apply u) := by vreact_auto
-- 3 chained ops
example (m : JSMap Int Int) (a b c : Int) (h : m.values.all (fun x => JS.le 0 x) = true) :
    (((m.set a 1).delete b).set c 3).values.all (fun x => JS.le 0 x) = true := by vreact_auto
example (m : JSMap Int Int) (a b c : Int) (habc : a ≠ b ∧ a ≠ c) :
    (((m.set a 1).delete b).set c 3).get a = some 1 := by vreact_auto
example (m : JSMap Int Int) (a b : Int) (h : m.has a = false) (hb : m.has b = false) (hab : a ≠ b) :
    ((m.set a 1).set b 2).size = m.size + 2 := by vreact_auto
end VReact.JSMapTest.T2
namespace VReact.JSMapTest.T3
open VReact VReact.JS
structure Ui where
  held : JSMap Int Int
  collapsed : JSSet JS.Str
deriving Repr, DecidableEq
structure M2 (K V : Type) where
  entries : List (K × V)
  nodup : (entries.map Prod.fst).Nodup
deriving DecidableEq
-- false goals: must fail
example : True := by
  vreact_fails_showing_goal (∀ (m : JSMap Int Int) (k v : Int), (m.set k v).size = m.size + 1)
  vreact_fails_showing_goal (∀ (m : JSMap Int Int) (k : Int), (m.delete k).size = m.size - 1)
  vreact_fails_showing_goal (∀ (a b c : Int), ((((JSMap.empty : JSMap Int Int).set 1 a).set 2 b).set 1 c).keys = [2, 1])
  vreact_fails_showing_goal (∀ (m : JSMap Int Int) (k k' v : Int), (m.set k v).get k' = some v)
  vreact_fails_showing_goal (∀ (s : JSSet Int) (x y : Int), (s.delete x).has y = s.has y)
  trivial
end VReact.JSMapTest.T3
namespace VReact.JSMapTest.T6
open VReact VReact.JS
set_option vreact.heartbeats 200000 in
example (m : JSMap Int Int) (a b c d k : Int) (h : m.has k = true) : ((((m.set a 1).set b 2).set c 3).set d 4).has k = true := by vreact_ob vreact_auto
set_option vreact.heartbeats 200000 in
example (m : JSMap Int Int) (a b c d k : Int) (h : m.has k = true) (hk : k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ d) : ((((m.delete a).delete b).set c 3).delete d).has k = true := by vreact_ob vreact_auto
set_option vreact.heartbeats 200000 in
example (m : JSMap Int Int) (a b c d : Int) (h : m.values.all (fun x => JS.le 0 x) = true) :
    ((((m.set a 1).delete b).set c 3).set d 4).values.all (fun x => JS.le 0 x) = true := by vreact_ob vreact_auto
set_option vreact.heartbeats 200000 in
example (m : JSMap Int Int) (a b c d : Int) :
    ((((m.set a 1).set b 2).set c 3).set d 4).size ≤ m.size + 4 := by vreact_ob vreact_auto
set_option vreact.heartbeats 200000 in
example (m : JSMap Int Int) (a b c d : Int) :
    ((((m.set a 1).set b 2).set c 3).set d 4).keys.length ≤ m.keys.length + 4 := by vreact_ob vreact_auto
end VReact.JSMapTest.T6
namespace VReact.JSMapTest.T7
open VReact VReact.JS
example (m : JSMap Int Int) (p : Int → Bool) (h : m.keys.Nodup) : (((JS.slice (m.keys.filter p) 1)).reverse.map Key.int).Nodup := by vreact_ob vreact_auto
example (m : JSMap Int JS.Str) (cmp : Int × JS.Str → Int × JS.Str → Int) (h : (m.entries.map Prod.fst).Nodup) :
    (((JS.toSorted m.entries cmp).filter (fun p => JS.lt 0 p.1)).map (fun p => Key.int p.1)).Nodup := by vreact_ob vreact_auto
example (s : JSSet Int) (p : Int → Bool) (h : s.elems.Nodup) : (((JS.slice (s.elems.filter p) 1)).reverse.map Key.int).Nodup := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k : Int) : ((m.delete k).entries.filter (fun p => JS.lt 0 p.2)).length ≤ (m.entries.filter (fun p => JS.lt 0 p.2)).length := by vreact_ob vreact_auto
end VReact.JSMapTest.T7
namespace VReact.JSMapTest.T8
open VReact VReact.JS
example (m : JSMap Int Int) (p : Int → Bool) : (((JS.slice (m.keys.filter p) 1)).reverse.map Key.int).Nodup := by vreact_ob vreact_auto
example (m : JSMap Int JS.Str) (cmp : Int × JS.Str → Int × JS.Str → Int) :
    (((JS.toSorted m.entries cmp).filter (fun p => JS.lt 0 p.1)).map (fun p => Key.int p.1)).Nodup := by vreact_ob vreact_auto
example (s : JSSet Int) (p : Int → Bool) : (((JS.slice (s.elems.filter p) 1)).reverse.map Key.int).Nodup := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k v : Int) (p : Int → Bool) : (((JS.slice ((m.set k v).keys.filter p) 1)).reverse.map Key.int).Nodup := by vreact_ob vreact_auto
end VReact.JSMapTest.T8
namespace VReact.JSMapTest.T9
open VReact VReact.JS
example (m : JSMap Int Int) (k v : Int) (p : Int → Bool) : (((JS.slice ((m.set k v).keys.filter p) 1)).reverse.map Key.int).Nodup := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k v : Int) (h : m.has k = false) : (m.set k v).keys = m.keys ++ [k] := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k v : Int) (h : m.has k = true) : (m.set k v).keys = m.keys := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k v : Int) (h : m.has k = false) : (m.set k v).keys.getLast? = some k := by vreact_ob vreact_auto
example (m : JSMap Int Int) (a b : Int) (ha : m.has a = false) (hb : m.has b = false) (hab : a ≠ b) : ((m.set a 1).set b 2).keys = m.keys ++ [a, b] := by vreact_ob vreact_auto
end VReact.JSMapTest.T9
namespace VReact.JSMapTest.T10
open VReact VReact.JS
example (m : JSMap Int Int) (k : Int) (h : m.values.all (fun x => JS.le 0 x) = true) : 0 ≤ (m.get k).getD 0 := by vreact_ob vreact_auto
example (xs : List Int) (h : xs.all (fun x => JS.le 0 x) = true) : 0 ≤ (xs.find? (fun x => JS.lt 3 x)).getD 0 := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k : Int) (h : m.values.all (fun x => JS.le 0 x) = true) : 0 ≤ (m.get k).getD 0 := by vreact_ob vreact_auto
example (xs : List Int) (h : xs.all (fun x => JS.le 0 x) = true) : 0 ≤ (xs.find? (fun x => JS.lt 3 x)).getD 0 := by vreact_ob vreact_auto
end VReact.JSMapTest.T10
namespace VReact.JSMapTest.T11
open VReact VReact.JS
example (m : JSMap Int Int) (k : Int) (hk : m.has k = true) : (m.get k).isSome = true := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k : Int) (hk : m.has k = true) (h : m.values.all (fun x => JS.le 0 x) = true) :
    0 ≤ Option.get (m.get k) (by simp [JSMap.has_def] at hk; cases hm : m.get k <;> simp_all [JSMap.get_eq_none_iff]) := by vreact_ob vreact_auto
example (m : JSMap Int Int) (k : Int) (h : m.values.all (fun x => JS.le 0 x) = true) :
    (match h₂ : m.get k with | some v => JS.le 0 v | none => true) = true := by vreact_ob vreact_auto
end VReact.JSMapTest.T11
namespace VReact.JSMapTest.T12
/-! Round-1 audit shapes: a value read with `get` is its key's entry; values of literal Maps and of
`new Map(pairs)` / filtered Maps; lengths of spreads; Sets inside Maps; `new Set(xs)` sizes. -/
open VReact VReact.JS
structure Item where
  id : Int
  title : JS.Str
  done : Bool
deriving DecidableEq
-- get ↦ entry (the key/id invariant)
example (s : JSMap Int Item) (id' : Int) (h_pre : ∀ tup ∈ s.entries, tup.1 = tup.2.id) (it : Item) (h : s.get id' = some it) :
    ∀ tup ∈ (s.set id' { it with done := !it.done }).entries, tup.1 = tup.2.id := by vreact_ob vreact_auto
example (s : JSMap Int Item) (id' : Int) (h_pre : (∀ tup ∈ s.entries, tup.1 = tup.2.id) ∧ id' ∈ s.keys) (hh) :
    (Option.get (s.get id') hh).id = id' := by vreact_ob vreact_auto
-- values of literal Maps and of a set on an empty Map
example : ∀ v ∈ (JSMap.ofList [((JS.Str.ofString "apple"), (1 : Int))]).values, v ≥ 0 := by vreact_ob vreact_auto
example : ∀ v ∈ (JSMap.ofList [((JS.Str.ofString "apple"), (1 : Int)), (JS.Str.ofString "pear", 2)]).values, v ≥ 0 := by vreact_ob vreact_auto
example (k : JS.Str) : ∀ v ∈ ((JSMap.empty : JSMap JS.Str Int).set k 1).values, v ≥ 0 := by vreact_ob vreact_auto
-- lengths of [...m], [...m.values()]
example (m : JSMap JS.Str Int) (h : m.size > 0) : 0 < m.entries.length := by vreact_ob vreact_auto
example (m : JSMap JS.Str Int) (h : m.size > 0) : 0 < m.values.length := by vreact_ob vreact_auto
example (m : JSMap Int Item) : (m.values.length : Int) = m.size ∧ (m.entries.length : Int) = m.size := by vreact_ob vreact_auto
-- index by id (new Map(pairs), the for…of loop of sets), filtered Maps, sizes
example (xs : List Item) : ∀ tup ∈ (JSMap.ofList (xs.map (fun x => (x.id, x)))).entries, tup.1 = tup.2.id := by vreact_ob vreact_auto
example (xs : List Item) : ∀ tup ∈ (xs.foldl (fun acc x => acc.set x.id x) (JSMap.empty : JSMap Int Item)).entries, tup.1 = tup.2.id := by vreact_ob vreact_auto
example (m : JSMap Int Item) : ∀ v ∈ (JSMap.ofList (m.entries.filter (fun p => !p.2.done))).values, v.done = false := by vreact_ob vreact_auto
example (m : JSMap Int Item) : (JSMap.ofList (m.entries.filter (fun p => !p.2.done))).size ≤ m.size := by vreact_ob vreact_auto
example (xs : List Item) (h : (xs.map (fun x => x.id)).Nodup) : (JSMap.ofList (xs.map (fun x => (x.id, x)))).size = xs.length := by vreact_ob vreact_auto
example (xs : List Int) (h : xs.Nodup) : (JSSet.ofList xs).size = xs.length := by vreact_ob vreact_auto
-- a loop adding the elements themselves (`for (const x of xs) n.add(x)`)
example (xs : List Int) : ∀ x ∈ xs, (xs.foldl (fun acc x => acc.add x) (JSSet.empty : JSSet Int)).has x = true := by vreact_ob vreact_auto
example (xs : List Int) : (xs.foldl (fun acc x => acc.add x) (JSSet.empty : JSSet Int)).size ≤ xs.length := by vreact_ob vreact_auto
example (xs : List Int) : (JSSet.ofList xs).size ≤ xs.length := by vreact_ob vreact_auto
-- Sets inside a Map (group membership)
example (g : JSMap JS.Str (JSSet Int)) (k : JS.Str) (x : Int) (hh) :
    (g.set k (((g.get k).getD JSSet.empty).add x)).has k = true ∧ ((g.set k (((g.get k).getD JSSet.empty).add x)).get k |>.get hh).has x = true := by vreact_ob vreact_auto
example (g : JSMap JS.Str (JSSet Int)) (k : JS.Str) (x : Int) (cur : JSSet Int) (hh) :
    (g.set k (cur.delete x)).has k = false ∨ ((g.set k (cur.delete x)).get k |>.get hh).has x = false := by vreact_ob vreact_auto
-- still false: the size of new Set(xs) without distinct elements, a value the filter drops,
-- the size of new Map(pairs) without distinct keys
example : True := by
  vreact_fails_showing_goal (∀ (xs : List Int), (JSSet.ofList xs).size = xs.length)
  vreact_fails_showing_goal (∀ (m : JSMap Int Item), ∀ v ∈ (JSMap.ofList (m.entries.filter (fun p => !p.2.done))).values, v.done = true)
  vreact_fails_showing_goal (∀ (xs : List Item), (JSMap.ofList (xs.map (fun x => (x.id, x)))).size = xs.length)
  trivial
end VReact.JSMapTest.T12

namespace VReact.JSMapTest.T13
open VReact VReact.JS
/-! Generic collection helpers: abstract keys `{K : Type} [DecidableEq K]` (an equality-constrained
type parameter), and the pigeonhole facts on Sets / Map keys (`sameMembers`, `sameKeys`). -/
-- toggleIn on an abstract Set: the toggled element, every other member unchanged
example {K : Type} [DecidableEq K] (s : JSSet K) (k : K) :
    (if s.has k = true then s.delete k else s.add k).has k = !s.has k := by vreact_ob vreact_auto
example {K : Type} [DecidableEq K] (s : JSSet K) (k : K) :
    ∀ x ∈ s.elems, x = k ∨ x ∈ (if s.has k = true then s.delete k else s.add k).elems := by vreact_ob vreact_auto
-- a Map update at an abstract key, compared through get (V with equality)
example {K V : Type} [DecidableEq K] [DecidableEq V] (m : JSMap K V) (k : K) (v : V) :
    (m.set k v).get k = some v ∧ ∀ p ∈ m.entries, p.1 = k ∨ (m.set k v).get p.1 = some p.2 := by vreact_ob vreact_auto
-- pigeonhole: one inclusion and equal sizes give the other inclusion; mutual inclusion, equal sizes
example {K : Type} [DecidableEq K] (a b : JSSet K) (h : (a.elems.all fun x => b.has x) = true) (hs : b.size ≤ a.size) :
    (b.elems.all fun x => a.has x) = true := by vreact_ob vreact_auto
example {K : Type} [DecidableEq K] (a b : JSSet K) (h : ∀ x ∈ a.elems, x ∈ b.elems) (h' : ∀ x ∈ b.elems, x ∈ a.elems) :
    a.size = b.size := by vreact_ob vreact_auto
example {K : Type} [DecidableEq K] (a b : JSSet K) :
    (JS.eq a.size b.size && a.elems.all (fun x => b.has x)) = (a.elems.all (fun x => b.has x) && b.elems.all (fun x => a.has x)) := by
  vreact_ob vreact_auto
example (a b : JSMap Int JS.Str) :
    (JS.eq a.size b.size && a.keys.all (fun x => b.has x)) = (a.keys.all (fun x => b.has x) && b.keys.all (fun x => a.has x)) := by
  vreact_ob vreact_auto
example (a b : JSSet Int) (x : Int) (h : ∀ y ∈ a.elems, y ∈ b.elems) (hb : b.has x = true) (ha : a.has x = false) :
    a.size < b.size := by vreact_ob vreact_auto
-- an index by a key function with distinct keys maps each element's key to the element
-- (also for an abstract element type with an accessor, as in a field-constrained generic)
example {T : Type} (T_id T_qty : T → Int) (xs : List T) (h : (xs.map (fun x => T_id x)).Nodup) :
    ∀ x ∈ xs, ((JSMap.ofList (xs.map (fun x => (T_id x, x)))).get (T_id x)).map T_qty = some (T_qty x) := by vreact_ob vreact_auto
structure Row where
  id : Int
  qty : Int
example (xs : List Row) (h : (xs.map (fun x => x.id)).Nodup) :
    ∀ x ∈ xs, (xs.foldl (fun acc x => acc.set x.id x) (JSMap.empty : JSMap Int Row)).get x.id = some x := by vreact_ob vreact_auto
-- still false: without the inclusion, or with sizes alone, nothing follows
example : True := by
  vreact_fails_showing_goal (∀ (a b : JSSet Int) (x : Int), a.has x = false → b.has x = true → a.size < b.size)
  vreact_fails_showing_goal (∀ (a b : JSSet Int), a.size = b.size → (b.elems.all fun x => a.has x) = true)
  vreact_fails_showing_goal (∀ (a b : JSMap Int Int), (a.keys.all fun x => b.has x) = true → (b.keys.all fun x => a.has x) = true)
  vreact_fails_showing_goal (∀ (xs : List Row), ∀ x ∈ xs, (JSMap.ofList (xs.map (fun x => (x.id, x)))).get x.id = some x)
  trivial
end VReact.JSMapTest.T13
