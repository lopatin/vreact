import VTS.m.Defs

/-- What the translation sees; the suite replaces this file with `smuggled/m.lean` (which the
whitelist rejects) before Lean runs. -/
theorem placeholder_m : True := trivial
