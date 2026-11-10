-- helpers
import VTS.m.Defs

theorem inca_pos (x : Int) : x < VTS.m.inca x := by unfold VTS.m.inca; omega
