import Proof.Quartic.StagePrintTuple.CostContracts
import Proof.Gates.WordPrograms.Sort

set_option autoImplicit false

namespace NearQuarticWires.StageTupleCensusBounds

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open StagePrint

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual Stack loader reads fixed-width signed fields,
five bounded work constants, and the four real unary dimensions. -/
theorem stack_loadCost (r : StackRequest) : r.loadCost=
    12*(r.tuples.length*(r.m*(r.s+1))*(2*(r.W+1)+1)+1+
      5*(2*(r.W+1)+1)+r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length)+93 := by
  simp only [StackRequest.loadCost,Top.loadCost,Top.loadRec,Top.loadChainCost,
    List.length_append,frame_length,List.length_replicate,List.length_nil,
    recStream_map_length,binary_length,stackNums_length]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual full signed Stack clock has exactly a
quadratic tuple-count factor, including the three real loaders, all
unary dimensions, signed multiplication and ordinary head reset. -/
theorem stackCostBound : StageTuple.StackCostBound := by
  refine ⟨10^8,6,by norm_num,by norm_num,fun r=>?_⟩
  let load:=fun W s m T : ℕ=>12*(T*(m*(s+1))*(2*(W+1)+1)+1+
    5*(2*(W+1)+1)+m*(s+1)+(s+1)+m+T)+93
  let dim:=fun s m T : ℕ=>(16*(m*(s+1))+14)+1+((16*(m*(s+1))+14)+1+
    ((16*(s+1)+14)+1+((16*(s+1)+14)+1+((16*m+14)+1+(16*T+14)))))
  let f:=fun W s m T : ℕ=>2*((load W s m T+1+(load W s m T+1+load W s m T))+1+
    (dim s m T+1+stackAllCost W (m*(s+1)) (s+1) m (T*(m*(s+1))) T))+2
  have heq : 2*r.budget+2=f r.W r.s r.m r.tuples.length := by
    rw [StackRequest.budget,stack_loadCost,stackNums_length]
    rfl
  let S:=r.W+r.s+r.m
  have hmono : f r.W r.s r.m r.tuples.length≤f S S S r.tuples.length := by
    dsimp only [f,load,dim]
    unfold stackAllCost stackOneCost baseCost sumBodyCost oneFieldCost fieldBodyCost SInt.smulCost
    gcongr <;> dsimp only [S] <;> omega
  have hpoly (S T : ℕ) : f S S S T≤10^8*(S+1)^6*(T+1)^2 := by
    dsimp only [f,load,dim]
    unfold stackAllCost stackOneCost baseCost sumBodyCost oneFieldCost fieldBodyCost SInt.smulCost
    ring_nf
    omega
  rw [heq]
  exact hmono.trans (hpoly S r.tuples.length)

end NearQuarticWires.StageTupleCensusBounds
