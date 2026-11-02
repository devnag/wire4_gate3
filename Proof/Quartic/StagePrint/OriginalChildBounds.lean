import Proof.Quartic.StagePrint.OriginalChildMachine
import Proof.Quartic.Cells.Children

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.ThresholdCompiler
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the compiler field width is enlarged for arithmetic while the input remains the original gate. -/
def originalFieldWidth (n B : ℕ) : ℕ := B + Nat.clog 2 (n+1) + 4

/-- `lem:print`, paper/paper.tex: the original weight mass obeys its input bit bound. -/
theorem originalWeightMass_le {n : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) (hB : GateBits B g) :
    totalL (List.ofFn g.weight) ≤ n * 2^B := by
  unfold totalL
  rw [List.map_ofFn,List.sum_ofFn]
  calc ∑ i, (g.weight i).natAbs ≤ ∑ _i : Fin n, 2^B :=
      Finset.sum_le_sum fun i _ => (hB.1 i).le
    _ = _ := by simp

/-- `lem:print`, paper/paper.tex: the original inclusive gate is supplied to the physical strict compiler with the exact threshold shift. -/
def originalChildRequest {n : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) (hB : GateBits B g) :
    OriginalChildRequest where
  W := originalFieldWidth n B
  weights := List.ofFn g.weight
  target := g.threshold - 1
  weights_fit := by
    have ht := originalWeightMass_le B g hB
    have hl : n+1 ≤ 2 ^ Nat.clog 2 (n+1) := Nat.le_pow_clog (by decide) _
    have hp : 1 ≤ 2^B := Nat.one_le_two_pow
    have hm := Nat.mul_le_mul_right (2^B) hl
    simp only [List.length_ofFn,originalFieldWidth,pow_add,pow_succ]
    nlinarith
  target_fit := by
    have ht := originalWeightMass_le B g hB
    have he := Int.natAbs_sub_le g.threshold 1
    have htheta := hB.2
    have he1 : (g.threshold-1).natAbs ≤ g.threshold.natAbs+1 := by simpa using he
    have hth : (g.threshold-1).natAbs ≤ 2^B := by
      omega
    have hl : n+1 ≤ 2 ^ Nat.clog 2 (n+1) := Nat.le_pow_clog (by decide) _
    have hp : 1 ≤ 2^B := Nat.one_le_two_pow
    have hm := Nat.mul_le_mul_right (2^B) hl
    simp only [originalFieldWidth,pow_add,pow_succ]
    nlinarith

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the physical constructor's list is the original disjoint child list, not the children of a flipped gate. -/
theorem originalChildRequest_children {n : ℕ} (B : ℕ) (g : NormalizedThresholdGate n) (hB : GateBits B g) :
    compileL (originalChildRequest B g hB).weights (originalChildRequest B g hB).target =
      (exactChildren g).map kidL := by
  exact (compileL_eq g.weight (g.threshold-1)).symm

/-- `lem:print`, paper/paper.tex: enlargement of physical arithmetic width leaves the sharp paper child census unchanged. -/
theorem originalChildRequest_length {n : ℕ} (hn : 0<n) (B : ℕ)
    (g : NormalizedThresholdGate n) (hB : GateBits B g) :
    (compileL (originalChildRequest B g hB).weights (originalChildRequest B g hB).target).length ≤
      NearQuarticWires.Cells.childCap n B := by
  rw [originalChildRequest_children,List.length_map]
  exact NearQuarticWires.Cells.exactChildren_length_childCap hn B g hB

end NearQuarticWires.StagePrint
