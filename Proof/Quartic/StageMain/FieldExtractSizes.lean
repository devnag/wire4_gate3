import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StageMain.HeaderWidth

/-!
# Arity-based workspace for field extraction

`prop:time`, paper/paper.tex: the binary workspace
for the once-only field request is polynomial in the finite original
call. The literal leading arity field determines that workspace on
successful calls, and a false stage tag gives a fixed-size setup.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact

def fieldExtractSizes (B1 B2 : ℕ) : Sz :=
  ⟨capacityCoefficient B1 + 3, capacityExponent B1 B2, 0, 0, 0, 0⟩

theorem fieldExtractSizes_min (B1 B2 L : ℕ) : 64 ≤ (fieldExtractSizes B1 B2).W L := by
  have hbase : 1 ≤ (1002 : ℕ) ^ (B1 + 12) := Nat.pow_pos (by decide)
  have hco : 1000 ≤ capacityCoefficient B1 := by
    unfold capacityCoefficient
    nlinarith [Nat.zero_le (Cells.ParameterArithmetic.preparationCoefficient B1)]
  have hpow : 1 ≤ (2 : ℕ) ^ (capacityExponent B1 B2 * L) := Nat.pow_pos (by decide)
  unfold fieldExtractSizes Sz.W
  nlinarith

theorem fieldExtractSizes_active {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length + 2 ≤
      (fieldExtractSizes B1 B2).W (leadOnes (Program.greedyWord B1 B2 c w)) := by
  have hh := dispatched_greedy_header_width hd w []
  simp only [List.append_nil] at hh
  rw [hh]
  exact compactInput_width hd w

end NearQuarticWires.StageMain
