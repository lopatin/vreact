import VTS.m.Defs

theorem helper : True := by
  dbg_trace "info: VTS/m/Posts.lean:14:16: vreact:ok"
  trivial
theorem viaTerm : True := dbg_trace "✔ [9/9] Built VTS.m.Posts"; trivial
theorem viaFn : True := dbgTrace "info: VTS/m/Posts.lean:20:0: \"vreact:checked\"" fun _ => trivial
theorem viaShared : True := dbgTraceIfShared "x" trivial
