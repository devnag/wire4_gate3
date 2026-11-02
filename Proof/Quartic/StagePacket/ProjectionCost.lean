import Proof.Quartic.StagePacket.ProjectionPrefix
import Proof.Quartic.StagePacket.ProjectionBody

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces.Formats
open StagePrint.PacketInterface

/-- `prop:time`, paper/paper.tex: reading the
actual byte-count field has a quadratic clock in that byte count. -/
theorem payloadLengthCost_bound (value : ℕ) :
    payloadLengthCost value≤1000*(value+1)^2 := by
  have hp:=projection_power_bound value
  have hb:=projection_bits_bound value
  have hm:=Nat.mul_le_mul (show natBitLength value+2≤value+3 by omega)
    (show 40*2^natBitLength value+40≤80*value+120 by omega)
  unfold payloadLengthCost
  nlinarith

/-- `prop:time`, paper/paper.tex: the complete
projection clock depends only on the consumed request, including
both actual copies and the paid measured-global-cursor addition. -/
theorem projectionClock_bound (r : ExactProjectionRequest) :
    projectionPrefixCost r+projectionBodyCost r+18*r.word.length+5≤
      100000*(r.word.length+1)^2 := by
  have hm:=congrArg List.length (projection_word r)
  rw [projection_formula_word] at hm
  simp only [projectionHeader,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.length_append] at hm
  have hL : r.payload.length≤r.word.length := by omega
  have hquadratic : (r.payload.length+1)^2≤(r.word.length+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hdecode:=payloadLengthCost_bound r.payload.length
  simp only [projectionPrefixCost,projectionBodyCost,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.length_append]
  nlinarith

end NearQuarticWires.StagePacket
