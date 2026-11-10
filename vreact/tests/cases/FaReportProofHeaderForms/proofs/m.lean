/- a /- nested -/ comment -/
-- a line comment: import Proofs.lemmas.Nope
import VTS.m.Defs import Proofs.lemmas.A
import
  Proofs.lemmas.B -- a trailing comment
import Proofs.«lemmas».C/- no space -/

theorem m_ok : (1 : Nat) = 1 ∧ (2 : Nat) = 2 ∧ (3 : Nat) = 3 := ⟨a_ok, b_ok, c_ok⟩
