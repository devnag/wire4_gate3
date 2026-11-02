import Proof.Quartic.StagePrint.OriginalChildPrinter

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearQuarticWires.StagePrint
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal original-child compiler has polynomial
running time in signed field width and original arity. -/
theorem original_compileCost_polynomial (W n : ℕ) :
    compileCost W n ≤ 1000000 * (W + n + 1) ^ 5 := by
  let H := W + n
  have hm : compileCost W n ≤ compileCost H H := by
    unfold compileCost preCost mainCost lvlCost headCost visitCost childCost bodyCost
      BinW.divCost NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost
    gcongr <;> dsimp [H] <;> omega
  have hc : compileCost H H ≤ 1000000 * (H + 1) ^ 5 := by
    unfold compileCost preCost mainCost lvlCost headCost visitCost childCost bodyCost
      BinW.divCost NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost
    ring_nf
    omega
  exact hm.trans hc

/-- `lem:print`, paper/paper.tex: the original
weight record stream has its exact framed binary length. -/
theorem original_weight_stream_length (r : OriginalChildRequest) :
    (recStream (r.weights.map fun z => binary (r.W + 1) (SInt.encS z))).length =
      r.weights.length * (2 * (r.W + 1) + 1) + 1 := by
  rw [recStream_length (r.W + 1) _ (by
    intro w hw
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hw
    exact binary_length _ _), List.length_map]

/-- `lem:print`, paper/paper.tex: the cold original
loader pays for the weight stream, threshold, constants and dimensions. -/
theorem originalChild_loadCost_eq (r : OriginalChildRequest) :
    r.loadCost = 12 * (r.weights.length * (2 * (r.W + 1) + 1) +
      r.weights.length + 9 * (2 * (r.W + 1) + 1)) + 105 := by
  unfold OriginalChildRequest.loadCost Top.loadCost Top.loadRec Top.loadChainCost
  simp only [List.length_append, NearCubicWires.RepairOrdinary.frame_length,
    binary_length, List.length_replicate]
  rw [original_weight_stream_length]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete cold original-child program, including
its three field loads and dimension read, has polynomial cost. -/
theorem originalChild_budget_polynomial (r : OriginalChildRequest) :
    r.budget ≤ 2000000 * (r.W + r.weights.length + 1) ^ 5 := by
  let H := r.W + r.weights.length
  have hm : r.budget ≤
      3 * (12 * (H * (2 * (H + 1) + 1) + H + 9 * (2 * (H + 1) + 1)) + 105) +
        16 * H + 18 + compileCost H H := by
    rw [OriginalChildRequest.budget, originalChild_loadCost_eq]
    unfold compileCost preCost mainCost lvlCost headCost visitCost childCost bodyCost
      BinW.divCost NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost
    have hW : r.W ≤ H := Nat.le_add_right _ _
    have hn : r.weights.length ≤ H := Nat.le_add_left _ _
    calc
      _ ≤ (12 * (H * (2 * (H + 1) + 1) + H + 9 * (2 * (H + 1) + 1)) + 105) + 1 +
          ((12 * (H * (2 * (H + 1) + 1) + H + 9 * (2 * (H + 1) + 1)) + 105) + 1 +
          ((12 * (H * (2 * (H + 1) + 1) + H + 9 * (2 * (H + 1) + 1)) + 105) + 1 +
          (16 * H + 14 + 1 + compileCost H H))) := by
        unfold compileCost preCost mainCost lvlCost headCost visitCost childCost bodyCost
          BinW.divCost NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost
        gcongr
      _ = _ := by
        unfold compileCost preCost mainCost lvlCost headCost visitCost childCost bodyCost
          BinW.divCost NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost
        ring
  have hc :
      3 * (12 * (H * (2 * (H + 1) + 1) + H + 9 * (2 * (H + 1) + 1)) + 105) +
        16 * H + 18 + compileCost H H ≤ 2000000 * (H + 1) ^ 5 := by
    unfold compileCost preCost mainCost lvlCost headCost visitCost childCost bodyCost
      BinW.divCost NearCubicWires.WireExponent3_5.UnionMachine.RegRat.mulCost
    ring_nf
    omega
  exact hm.trans hc

/-- `lem:print` and `prop:time`, paper/paper.tex: final physical output framing preserves the
polynomial running time of the cold original-child word function. -/
theorem originalChildPrinter_budget_polynomial (r : OriginalChildRequest) :
    2 * r.budget + 2 ≤ 4000002 * (r.W + r.weights.length + 1) ^ 5 := by
  have hb := originalChild_budget_polynomial r
  have hp : 1 ≤ (r.W + r.weights.length + 1) ^ 5 := Nat.pow_pos (by omega)
  nlinarith only [hb, hp]

end NearQuarticWires.Cells.ParameterArithmetic
