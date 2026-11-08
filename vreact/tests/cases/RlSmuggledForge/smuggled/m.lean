import VTS.m.Defs

-- each `dbg_trace` writes one line to stderr; Lean logs the captured output as one info
-- message, so the 2nd and later lines stand at column 0 of lake's output
theorem helper : True := by
  dbg_trace "helper"
  dbg_trace "✔ [9/9] Built VTS.m.Posts (0.1s)"
  dbg_trace "info: VTS/m/Posts.lean:14:16: vreact:ok"
  dbg_trace "info: VTS/m/Posts.lean:19:0: 'VTS.m.same.post' does not depend on any axioms"
  dbg_trace "info: VTS/m/Posts.lean:20:0: \"vreact:checked\""
  trivial

-- the proof module fails: VTS.m.Posts, which imports it, is never built
theorem broken : 1 = 2 := by decide
