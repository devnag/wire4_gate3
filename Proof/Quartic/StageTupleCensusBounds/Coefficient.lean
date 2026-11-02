import Proof.Quartic.StageTupleCensusBounds.SmallBudget

set_option autoImplicit false

namespace NearQuarticWires.StageTupleCensusBounds

open NearCubicWires NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageTuple

/-- `lem:print` and `prop:time`, paper/paper.tex: actual signed conversion and both cold framing stages
are polynomial in only their own width and canonical coefficient packet. -/
theorem coefficientCostBound : StageTuple.CoefficientCostBound := by
  refine ⟨10^21,10,by norm_num,by norm_num,fun r=>?_⟩
  let S:=r.width+(intWord r.coefficient).length
  have hbit:=natBitLength_le_succ r.width
  have hword : r.word.length≤2*S+3 := by
    simp only [CoefficientRequest.word,List.length_append,natWord_length]
    dsimp only [S]
    omega
  have hsteps : r.steps≤60*S+230 := by
    unfold CoefficientRequest.steps
    dsimp only [S]
    omega
  have hlen : r.word.length+1≤2*S+4 := by omega
  have hcount : r.steps+1≤60*S+231 := by omega
  have hsmall:=dispatch_budget VV r.word.length r.steps
  have hbound : r.budget≤1600*(2*S+4)+4*(10^8*258*(2*S+4)^8*(60*S+231))+12 := by
    unfold CoefficientRequest.budget CoefficientRequest.arithmeticBudget
    calc
      _≤1600*(r.word.length+1)+4*(10^8*(VV+2)*(r.word.length+1)^8*(r.steps+1))+12 := by gcongr
      _≤_ := by norm_num only [VV];gcongr
  have hpoly (S : ℕ) :
      1600*(2*S+4)+4*(10^8*258*(2*S+4)^8*(60*S+231))+12≤10^21*(S+1)^10 := by
    ring_nf
    omega
  exact hbound.trans (hpoly S)

end NearQuarticWires.StageTupleCensusBounds
