import Proof.Quartic.StageMain.RuntimeArithmetic

/-!
# Full main clock on a dispatched call

`prop:time`, paper/paper.tex: the literal composed
budget is a fixed polynomial times the sample census plus the once-only
field-search factor. Both copied streams and every compiled source step
are included in this inequality.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact Controller Bounds StageLift

theorem mainBudget_active_bound {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (hr : parameterReadCost p.1 (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤
      20000 * (runtimeScale f K d c.n) ^ 2) :
    mainBudgetWithEntry f K d c w ≤ 10000000000000 * (runtimeScale f K d c.n) ^ 5 *
      (2 ^ (c.n - p.1.k) * p.1.Q + 2 ^ (2 * p.1.ellf)) := by
  let S := runtimeScale f K d c.n
  let N := 2 ^ (c.n - p.1.k) * p.1.Q
  have hS : 1 ≤ S := by dsimp only [S, runtimeScale]; omega
  have hQ : 1 ≤ p.1.Q := by rw [(Cells.prepare_spec _ p.1 p.2).Q_eq]; exact Nat.one_le_two_pow
  have hN : 1 ≤ N := Nat.mul_pos (Nat.two_pow_pos _) hQ
  have hR := runtimeScale_envelope f K d c.n
  have hc : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ S := by
    have hh := (compact_le K d hd w).trans hR
    rwa [prepWord_eq_compact hd] at hh
  have he : p.1.ellf ≤ S := ((scalar_le K d hd).1).trans hR
  have hm : (Program.mainWord B1 B2 c w).length ≤ 400 * S :=
    (mainWord_le K d hd w).trans (Nat.mul_le_mul_left _ hR)
  have hhead := dispatched_greedy_header_width hd w (mainFieldBits B1 B2 c)
  change leadOnes (cachedMainWord B1 B2 c w) = 1 + natBitLength c.n at hhead
  have hhead0 := dispatched_greedy_header_width hd w []
  simp only [List.append_nil] at hhead0
  have hT : mainStepLimit B1 B2 K d c w ≤ 100 * S := by
    unfold mainStepLimit
    rw [hhead]
    apply Nat.mul_le_mul_left
    dsimp only [S, runtimeScale]
    omega
  have hsrc := sourceSteps_le hd w _ S hS hT hc he hm hr
  have hi : (cachedMainWord B1 B2 c w).length ≤ 25 * S * N := cached_length_le hd w S hS hc he
  have hi0 : (Program.greedyWord B1 B2 c w).length ≤ 25 * S * N := by
    have hh : (Program.greedyWord B1 B2 c w).length ≤ (cachedMainWord B1 B2 c w).length := by
      simp only [cachedMainWord, List.length_append]; omega
    exact hh.trans hi
  have hcompiled : cachedMainBudget f (mainSizes B1 B2 K d) (mainStepLimit B1 B2 K d) c w ≤
      40000000000 * S ^ 5 * N := by
    apply (main_langBudget_le f K d c.n _ hhead _).trans
    calc
      _ ≤ 10000 * S ^ 2 * (3000000 * S ^ 3 * N + 25 * S * N + 1) := by gcongr
      _ ≤ _ := (compiled_clock_arithmetic 3000000 S N hS hN).trans (by gcongr; norm_num)
  have hexsrc := extractFieldSteps_le hd w S hS hc he hr
  have hexN : extractFieldSteps B1 B2 c w ≤ 101000 * S ^ 3 * N :=
    hexsrc.trans (Nat.le_mul_of_pos_right _ hN)
  have hex : fieldExtractCost B1 B2 c w ≤ 2000000000 * S ^ 5 * N := by
    apply (extraction_langBudget_le f K d c.n _ hhead0 _).trans
    calc
      _ ≤ 10000 * S ^ 2 * (101000 * S ^ 3 * N + 25 * S * N + 1) := by gcongr
      _ ≤ _ := (compiled_clock_arithmetic 101000 S N hS hN).trans (by gcongr; norm_num)
  have hval : (mainFieldRequest B1 B2 c).val = p.1.ellf := by
    simp only [mainFieldRequest, mainFieldDegree, hd]
  have hfield : fieldSetupCost (mainFieldRequest B1 B2 c) ≤ 2000 * S * 2 ^ (2 * p.1.ellf) := by
    have hh := setup_clock_le (mainFieldRequest B1 B2 c)
    rw [hval] at hh
    calc
      _ ≤ 1000 * (2 ^ (2 * p.1.ellf) * (2 * S)) := hh.trans (Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (by omega)))
      _ = _ := by ring
  have hcache : (mainFieldBits B1 B2 c).length ≤ S := by
    simpa only [mainFieldBits, mainFieldDegree, hd, binary_length] using he
  exact composition_clock_arithmetic _ _ _ _ _ S N _ hS hN Nat.one_le_two_pow
    hex hcompiled hfield hi0 hcache

end NearQuarticWires.StageMain.Runtime
