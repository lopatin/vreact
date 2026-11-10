import VTS.m.Defs

/-- False: `omega` fails, so this file (and Posts.lean, which imports it) does not build. -/
theorem broken (x : Int) : x + 1 = x := by
  omega
