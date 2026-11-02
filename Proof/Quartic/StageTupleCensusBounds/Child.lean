import Proof.Quartic.StagePrintTuple.CostContracts
import Proof.Gates.WordPrograms.Sort

set_option autoImplicit false

namespace NearQuarticWires.StageTupleCensusBounds

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open StagePrint

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold child loader's clock is affine in
its genuine fixed-width record counts and four unary dimensions. -/
theorem child_loadCost (r : ChildTupleRequest) : r.loadCost=
    12*(r.children.length*r.N*(2*r.L+1)+1+
      (r.tuples.length*r.M*(2*r.L+1)+1)+r.N+r.M+r.children.length+r.tuples.length)+93 := by
  simp only [ChildTupleRequest.loadCost,Top.loadCost,Top.loadRec,Top.loadChainCost,
    List.length_append,frame_length,List.length_replicate,List.length_nil,
    recStream_map_length,fieldNums_length _ _ r.children_length,fieldNums_length _ _ r.tuples_length]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual complete Cartesian word-function clock
retains exactly quadratic child and old-tuple factors, including loading,
all dimension reads, sequential copying and the final head return. -/
theorem childTupleCostBound : StageTuple.ChildTupleCostBound := by
  refine ⟨10^6,4,by norm_num,by norm_num,fun r=>?_⟩
  let f:=fun L N M K T : ℕ=>
    2*(12*(K*N*(2*L+1)+1+(T*M*(2*L+1)+1)+N+M+K+T)+93+1+
      (16*N+14+1+(16*M+14+1+(16*K+14+1+(16*T+14)))+1+tupleCost L N M K T))+2
  have heq : 2*r.budget+2=f r.L r.N r.M r.children.length r.tuples.length := by
    rw [ChildTupleRequest.budget,child_loadCost]
    rfl
  let S:=r.L+r.N+r.M
  have hmono : f r.L r.N r.M r.children.length r.tuples.length≤
      f S S S r.children.length r.tuples.length := by
    dsimp only [f]
    unfold tupleCost tOuterCost tInnerCost copyStep
    gcongr <;> dsimp only [S] <;> omega
  have hpoly (S K T : ℕ) : f S S S K T≤10^6*(S+1)^4*(K+1)^2*(T+1)^2 := by
    dsimp only [f]
    unfold tupleCost tOuterCost tInnerCost copyStep
    ring_nf
    omega
  rw [heq]
  exact hmono.trans (hpoly S r.children.length r.tuples.length)

end NearQuarticWires.StageTupleCensusBounds
