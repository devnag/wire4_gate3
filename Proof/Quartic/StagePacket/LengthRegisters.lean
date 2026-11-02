import Proof.Quartic.StagePacket.Isolation

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {nr : ℕ}

/-- `prop:time`, paper/paper.tex: the actual
payload-length reader uses fixed distinct scratch registers. -/
def lengthSlots : Fin 8 ↪ Fin 16 where
  toFun i:=![5,6,7,8,10,12,9,13] i
  inj':=by decide

/-- `prop:time`, paper/paper.tex: the existing
binary-length kernel is embedded in the projection's actual bank. -/
def lengthRegisters (R : Fin 16 ↪ Fin nr) : Fin 8 ↪ Fin nr where
  toFun i:=R (lengthSlots i)
  inj':=R.injective.comp lengthSlots.injective

/-- `prop:time`, paper/paper.tex: every named
projection register is distinct at its original actual position. -/
theorem register_ne (R : Fin 16 ↪ Fin nr) {i j : Fin 16} (h : i≠j) : R i≠R j := R.injective.ne h

end NearQuarticWires.StagePacket
