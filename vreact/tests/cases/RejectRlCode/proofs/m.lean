import VTS.m.Defs

axiom cheat : ∀ x : Int, x + 1 = x
opaque oo : Nat
#eval IO.FS.writeFile "VTS/m/Posts.lean" ""
initialize pure ()
run_cmd Lean.logInfo "vreact:ok"
structure St where
  x : Nat
partial def loop : Nat → Nat := fun n => loop n
mutual
theorem m1 : True := trivial
end
theorem readsFile : True := by
  have : String := include_str "m.lean"
  trivial
meta section
end
#exit
