import Proof.Quartic.StageMain.RuntimeCompile

/-!
# Constant main cost on the completed-interval branch

`sec:algorithm`, paper/paper.tex:
a false dispatch tag carries a completed interval. The main pass only
copies that bounded interval and uses fixed arithmetic reservations;
the encoded arity of the original call does not enter this branch.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact Bounds StageLift Controller

noncomputable def defaultScale {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ) : ℕ :=
  mainSizeCoefficient B1 K + mainSizeDegree B1 B2 d + capacityCoefficient B1 + capacityExponent B1 B2 +
    TSK (sampleTaggedCallee f) + TSK StageGamma.fieldProducerCallee + VV + MM + 1000

noncomputable def defaultClock {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ) : ℕ :=
  let S := defaultScale f K d
  4 * (2 * (2 * (4 * (10000 * S ^ 2 * 46) + 4 * fieldSetupCost ⟨1, by decide⟩ + 12) +
    150 * (25 + 1 + 1)) + 2) + 4 * (10000 * S ^ 2 * 50047) + 12

theorem mainBudget_none_le {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    {c : Call} (hd : Program.dispatch B1 B2 c = none) (w : List Bool) :
    mainBudgetWithEntry f K d c w ≤ defaultClock f K d := by
  let S := defaultScale f K d
  have hS : 1 ≤ S := by dsimp only [S, defaultScale]; omega
  have h0 := nondispatched_greedy_header_width hd w []
  simp only [List.append_nil] at h0
  have hh := nondispatched_greedy_header_width hd w (mainFieldBits B1 B2 c)
  change leadOnes (cachedMainWord B1 B2 c w) = 0 at hh
  have hinput : (Program.greedyWord B1 B2 c w).length ≤ 25 := by
    have h := Cells.nondispatched_outputWord_length c w hd
    simpa only [Program.greedyWord, Program.stageWord, hd, List.length_cons] using Nat.succ_le_succ h
  have hcache : (mainFieldBits B1 B2 c).length = 1 := by
    simp only [mainFieldBits, mainFieldDegree, hd, binary_length]
  have hcached : (cachedMainWord B1 B2 c w).length ≤ 26 := by
    simp only [cachedMainWord, List.length_append, hcache]; omega
  have hex : fieldExtractCost B1 B2 c w ≤ 10000 * S ^ 2 * 46 := by
    have hbound := langBudget_le StageGamma.fieldProducerCallee (fieldExtractSizes B1 B2)
      VV MM (Program.greedyWord B1 B2 c w) 20 S hS
      (by dsimp only [S, defaultScale]; omega) (by dsimp only [S, defaultScale]; omega)
      (by dsimp only [S, defaultScale]; omega)
      (by change capacityCoefficient B1 + 3 ≤ S; dsimp only [S, defaultScale]; omega)
      (by change capacityExponent B1 B2 ≤ S; dsimp only [S, defaultScale]; omega)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      (by rw [h0]; omega)
      (by rw [h0]; simp only [fieldExtractSizes, Sz.W, Nat.mul_zero, pow_zero, one_mul]
          dsimp only [S, defaultScale]; omega)
      (by simp [fieldExtractSizes, Sz.Lk]) (by simp [fieldExtractSizes, Sz.Bk])
    simp only [fieldExtractCost, extractFieldSteps, hd]
    exact hbound.trans (Nat.mul_le_mul_left _ (by omega))
  have hy : cachedMainBudget f (mainSizes B1 B2 K d) (mainStepLimit B1 B2 K d) c w ≤
      10000 * S ^ 2 * 50047 := by
    have ha : mainSizeCoefficient B1 K ≤ S := by dsimp only [S, defaultScale]; omega
    have he : mainSizeDegree B1 B2 d ≤ S := by dsimp only [S, defaultScale]; omega
    have hw : (mainSizes B1 B2 K d).W (leadOnes (cachedMainWord B1 B2 c w)) ≤ S := by
      rw [hh]
      simpa only [mainSizes, Sz.W, Nat.mul_zero, pow_zero, one_mul] using ha
    have hbound := langBudget_le (sampleTaggedCallee f) (mainSizes B1 B2 K d)
      VV MM (cachedMainWord B1 B2 c w) 50020 S hS
      (by dsimp only [S, defaultScale]; omega) (by dsimp only [S, defaultScale]; omega)
      (by dsimp only [S, defaultScale]; omega) ha he ha he ha he (by rw [hh]; omega) hw hw hw
    simp only [cachedMainBudget, sourceSteps, hd]
    exact hbound.trans (Nat.mul_le_mul_left _ (by omega))
  have hf : mainFieldRequest B1 B2 c = ⟨1, by decide⟩ := by
    apply Subtype.ext
    simp only [mainFieldRequest, mainFieldDegree, hd]
  unfold mainBudgetWithEntry mainBudgetOf retainedMainFieldCost mainFieldCost defaultClock
  rw [hf, hcache]
  change _ ≤ 4 * (2 * (2 * (4 * (10000 * S ^ 2 * 46) + 4 * fieldSetupCost ⟨1, by decide⟩ + 12) +
    150 * (25 + 1 + 1)) + 2) + 4 * (10000 * S ^ 2 * 50047) + 12
  gcongr

end NearQuarticWires.StageMain.Runtime
