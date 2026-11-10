import VTS.a.Defs
-- lemmas about b too (/- see below)
import VTS.b.Defs

theorem inca_gt (x : Int) : x < VTS.a.inca x := by unfold VTS.a.inca; omega
theorem twice_unfold (x : Int) : VTS.b.twice x = VTS.a.inca (VTS.a.inca x) := rfl
-- end -/
