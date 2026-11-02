import Proof.Quartic.StageTupleCensusBounds.SmallBudget

set_option autoImplicit false

namespace NearQuarticWires.StageTupleCensusBounds

open NearCubicWires NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageTuple

/-- `lem:print` and `prop:time`, paper/paper.tex: the real finite support-prefix search, source framing,
compiled arithmetic and final output framing are charged solely to
one support cache and its genuine finite position. -/
theorem supportIndexCostBound : StageTuple.SupportIndexCostBound := by
  refine ⟨10^32,14,by norm_num,by norm_num,fun r=>?_⟩
  let S:=r.support.length+(listWord NearCubicWires.RepairRepresentation.natWord r.support).length
  have hi : r.index.val≤S := by have hh:=r.index.isLt;dsimp only [S];omega
  have hbit:=natBitLength_le_succ r.index.val
  have hword : r.word.length≤2*S+3 := by
    simp only [SupportIndexRequest.word,List.length_append,natWord_length]
    dsimp only [S] at hi ⊢
    have hh:=r.index.isLt
    omega
  have hwidth : (ctxOf 4 r.word []).Wd≤(2*S+7)^4 := by
    change (r.word.length+4)^4≤_
    exact Nat.pow_le_pow_left (by omega) _
  let stepMajor:=3*(S*(30*(2*S+7)^4+64)+200*(2*S+7)^4+400)+2
  have hsteps : 3*r.steps (ctxOf 4 r.word [])+2≤ stepMajor := by
    unfold SupportIndexRequest.steps
    dsimp only [stepMajor]
    gcongr
  have hlen : r.word.length+1≤2*S+4 := by omega
  have hcount : 3*r.steps (ctxOf 4 r.word [])+2+1≤ stepMajor+1 := by omega
  have hsmall:=dispatch_budget VV r.word.length (3*r.steps (ctxOf 4 r.word [])+2)
  have hbound : r.budget≤1600*(2*S+4)+4*(10^8*258*(2*S+4)^8*(stepMajor+1))+12 := by
    unfold SupportIndexRequest.budget SupportIndexRequest.arithmeticBudget
    calc
      _≤1600*(r.word.length+1)+4*(10^8*(VV+2)*(r.word.length+1)^8*
        (3*r.steps (ctxOf 4 r.word [])+2+1))+12 := by gcongr
      _≤_ := by norm_num only [VV];gcongr
  have hpoly (S : ℕ) :
      1600*(2*S+4)+4*(10^8*258*(2*S+4)^8*
        (3*(S*(30*(2*S+7)^4+64)+200*(2*S+7)^4+400)+2+1))+12≤10^32*(S+1)^14 := by
    ring_nf
    omega
  exact hbound.trans (hpoly S)

end NearQuarticWires.StageTupleCensusBounds
