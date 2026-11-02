import Proof.Quartic.StageMain.RuntimeSizes

/-!
# Actual compiler budgets at the common main width

`prop:time`, paper/paper.tex, includes the setup
and teardown of both arithmetic stages. Their widths depend on the
same raw arity header, and their input streams enter these bounds
only through their physically copied lengths.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CounterMachine.PrefixProg
open Compact Bounds StageLift

theorem main_langBudget_le {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d n : ℕ)
    (input : List Bool) (hhead : leadOnes input = 1 + natBitLength n) (N : ℕ) :
    langBudget (sampleTaggedCallee f) (mainSizes B1 B2 K d) VV MM input N ≤
      10000 * (runtimeScale f K d n) ^ 2 * (N + input.length + 1) := by
  let S := runtimeScale f K d n
  have hw : (mainSizes B1 B2 K d).W (leadOnes input) ≤ S := by
    rw [hhead]
    dsimp only [S, runtimeScale]
    omega
  have ha : mainSizeCoefficient B1 K ≤ S := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hw
  have hdeg : mainSizeDegree B1 B2 d ≤ S := by dsimp only [S, runtimeScale]; omega
  have hL : leadOnes input ≤ S := by
    rw [hhead]
    have hh := nbl_le_self' n
    dsimp only [S, runtimeScale]
    omega
  apply langBudget_le
  · dsimp only [S, runtimeScale]; omega
  · dsimp only [S, runtimeScale]; omega
  · dsimp only [S, runtimeScale]; omega
  · dsimp only [S, runtimeScale]; omega
  · exact ha
  · exact hdeg
  · exact ha
  · exact hdeg
  · exact ha
  · exact hdeg
  · exact hL
  · exact hw
  · exact hw
  · exact hw

theorem extraction_langBudget_le {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d n : ℕ)
    (input : List Bool) (hhead : leadOnes input = 1 + natBitLength n) (N : ℕ) :
    langBudget StageGamma.fieldProducerCallee (fieldExtractSizes B1 B2) VV MM input N ≤
      10000 * (runtimeScale f K d n) ^ 2 * (N + input.length + 1) := by
  let S := runtimeScale f K d n
  have hw : (fieldExtractSizes B1 B2).W (leadOnes input) ≤ S := by
    apply (extraction_width_le B1 B2 K d _).trans
    rw [hhead]
    dsimp only [S, runtimeScale]
    omega
  have ha : capacityCoefficient B1 + 3 ≤ S := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans hw
  have hdeg : capacityExponent B1 B2 ≤ S := by
    have hh : capacityExponent B1 B2 ≤ mainSizeDegree B1 B2 d := by
      unfold mainSizeDegree degree; omega
    dsimp only [S, runtimeScale]
    omega
  have hL : leadOnes input ≤ S := by
    rw [hhead]
    have hh := nbl_le_self' n
    dsimp only [S, runtimeScale]
    omega
  apply langBudget_le
  · dsimp only [S, runtimeScale]; omega
  · dsimp only [S, runtimeScale]; omega
  · dsimp only [S, runtimeScale]; omega
  · dsimp only [S, runtimeScale]; omega
  · exact ha
  · exact hdeg
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact hL
  · exact hw
  · simp [fieldExtractSizes, Sz.Lk]
  · simp [fieldExtractSizes, Sz.Bk]

end NearQuarticWires.StageMain.Runtime
