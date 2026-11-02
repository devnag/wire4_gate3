import Proof.Quartic.StageLiftTokens.Bounds
import Proof.Quartic.StageCert.DigitOccurrence

/-!
# Exact digit-coefficient ranges

`eq:testE` and `lem:print`, paper/paper.tex: a signed digit coefficient subtracts an actual retained
rate times a Boolean predecessor from a Boolean current value.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicGates.Close.Cells StageCert.Tokens

theorem selectedSummand_le (circuit firstCount g v : ℕ) :
    selectedSummand circuit firstCount g v≤v := by
  unfold selectedSummand
  split_ifs <;> omega

theorem sourceDigitPositive_le_one (bits : List Bool) (G row J k g : ℕ) :
    sourceDigitPositive bits G row J k g≤1 := by
  unfold sourceDigitPositive
  split_ifs <;> first | omega | cases bits.getD ((row+1)*G+k+g) false <;> decide

theorem source_rate_bound (factors : List ℕ) (E row : ℕ)
    (hf : ∀v∈factors,v≤2^E) :
    (if row=0 then 1 else factors.getD (row-1) 0)≤2^E := by
  split_ifs
  · exact Nat.one_le_pow _ _ (by decide)
  · by_cases hi : row-1<factors.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hf _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _

theorem source_coefficient_bits (bits : List Bool) (factors : List ℕ)
    (E G row J k g circuit firstCount : ℕ) (hE : 2≤E)
    (hf : ∀v∈factors,v≤2^E) :
    natBitLength (((selectedSummand circuit firstCount g
      (sourceDigitPositive bits G row J k g):ℤ)-selectedSummand circuit firstCount g
      (sourceDigitNegative bits factors G row J k g)).natAbs)≤ sourceBits E := by
  have hp := (selectedSummand_le circuit firstCount g _).trans
    (sourceDigitPositive_le_one bits G row J k g)
  have hn : selectedSummand circuit firstCount g (sourceDigitNegative bits factors G row J k g)≤2^E := by
    apply (selectedSummand_le circuit firstCount g _).trans
    unfold sourceDigitNegative
    exact (Nat.mul_le_mul_right _ (predecessorBit_le_one bits G row J k g)).trans
      (by simpa only [one_mul] using source_rate_bound factors E row hf)
  have habs := Int.natAbs_sub_le
    (selectedSummand circuit firstCount g (sourceDigitPositive bits G row J k g):ℤ)
    (selectedSummand circuit firstCount g (sourceDigitNegative bits factors G row J k g):ℤ)
  simp only [Int.natAbs_natCast] at habs
  apply nbl_le_of_lt _ (by unfold sourceBits; nlinarith)
  calc
    _ ≤1+2^E := habs.trans (Nat.add_le_add hp hn)
    _ ≤2^(E+1) := by
      have h := Nat.one_le_pow E 2 (by decide)
      rw [pow_succ]
      omega
    _ <2^(sourceBits E) := Nat.pow_lt_pow_right (by decide) (by unfold sourceBits; nlinarith)

end NearQuarticWires.StageLiftTokens
