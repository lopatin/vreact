import VTS.model.Defs
open VReact

-- "the total never exceeds the cap": an assumption, not a proof
axiom openQty_le_cap (os : List VTS.model.Order) : VTS.model.openQty os ≤ 1000
