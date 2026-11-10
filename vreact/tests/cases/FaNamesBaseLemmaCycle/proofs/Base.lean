import VTS.Base.Defs

theorem inca_pos (x : Int) : x < VTS.Base.inca x := by unfold VTS.Base.inca; omega
