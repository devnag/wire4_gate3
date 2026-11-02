import Proof.Quartic.StageMainMask.StructuralRuntime

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact

/-- `prop:time`, paper/paper.tex: a common
arity-header scale includes the actual arithmetic width and fixed
machine dimensions for the complete structural procedure. -/
noncomputable def structuralScale (B1 B2 n : ℕ) : ℕ :=
  (structuralSizes B1 B2).W (1 + natBitLength n) + capacityExponent B1 B2 +
    TSK StageGamma.fieldProducerCallee + VV + MM + n + 1000

/-- `prop:time`, paper/paper.tex: the compiler
budget remains linear in the actual formatter source clock and word
length, with quadratic width overhead. -/
theorem structuralFormatterBudget_le {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    structuralFormatterBudget r ≤ 4000000000 * (structuralScale B1 B2 r.call.n) ^ 5 := by
  let S := structuralScale B1 B2 r.call.n
  have hS : 1 ≤ S := by dsimp only [S, structuralScale]; omega
  have hw : (structuralSizes B1 B2).W (leadOnes (structuralWord r)) ≤ S := by
    rw [structural_header]
    dsimp only [S, structuralScale]
    omega
  have ha : 10 * (capacityCoefficient B1 + 3) ≤ S := by
    have hh : 10 * (capacityCoefficient B1 + 3) ≤
        (structuralSizes B1 B2).W (leadOnes (structuralWord r)) := by
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    exact hh.trans hw
  have hd : capacityExponent B1 B2 ≤ S := by dsimp only [S, structuralScale]; omega
  have hh : leadOnes (structuralWord r) ≤ S := by
    rw [structural_header]
    have hn := NearCubicGates.Close.CounterMachine.PrefixProg.nbl_le_self' r.call.n
    dsimp only [S, structuralScale]
    omega
  have hs : (structuralWord r).length ≤ S := (by have := structuralSizes_width r; omega :
      (structuralWord r).length ≤ (structuralSizes B1 B2).W (leadOnes (structuralWord r))).trans hw
  have hcompile : structuralFormatterBudget r ≤ 10000 * S ^ 2 *
      (3 * structuralFormatterSteps r + 8 + (structuralWord r).length + 1) := by
    apply StageMain.Runtime.langBudget_le
    · exact hS
    · dsimp only [S, structuralScale]; omega
    · dsimp only [S, structuralScale]; omega
    · dsimp only [S, structuralScale]; omega
    · exact ha
    · exact hd
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact hh
    · exact hw
    · simp [structuralSizes, Sz.Lk]
    · simp [structuralSizes, Sz.Bk]
  have hn := structuralFormatterSteps_le r S hS hs
  have hS3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have h03 : 1 ≤ S ^ 3 := Nat.pow_pos hS
  have hsum : 3 * structuralFormatterSteps r + 8 + (structuralWord r).length + 1 ≤
      330010 * S ^ 3 := by omega
  calc
    _ ≤ 10000 * S ^ 2 * (3 * structuralFormatterSteps r + 8 + (structuralWord r).length + 1) := hcompile
    _ ≤ 10000 * S ^ 2 * (330010 * S ^ 3) := Nat.mul_le_mul_left _ hsum
    _ ≤ 4000000000 * S ^ 5 := by ring_nf; omega

/-- `prop:time`, paper/paper.tex: acquisition,
compiled scanning and the physical handoff all have a single fixed
polynomial in the actual arity-header scale. -/
theorem structuralBudget_scale : ∃ K : ℕ, ∀ (B1 B2 : ℕ) (r : StructuralRequest B1 B2),
    structuralBudget r ≤ K * (structuralScale B1 B2 r.call.n) ^ 12 := by
  obtain ⟨Kr, hKr⟩ := structuralRawBudget_polynomial
  refine ⟨4 * 4000000000 + 4 * Kr * 33 ^ 12 + 12, ?_⟩
  intro B1 B2 r
  let S := structuralScale B1 B2 r.call.n
  have hS : 1 ≤ S := by dsimp only [S, structuralScale]; omega
  have hw : (structuralSizes B1 B2).W (leadOnes (structuralWord r)) ≤ S := by
    rw [structural_header]
    dsimp only [S, structuralScale]
    omega
  have hs : (structuralWord r).length ≤ S := by have := structuralSizes_width r; omega
  have hrawlen : (structuralRawRequest r).word.length + 1 ≤ 33 * S := by
    have := structuralRawRequest_length r
    omega
  have hraw : structuralRawBudget (structuralRawRequest r) ≤ Kr * 33 ^ 12 * S ^ 12 := by
    calc
      _ ≤ Kr * ((structuralRawRequest r).word.length + 1) ^ 12 := hKr _
      _ ≤ Kr * (33 * S) ^ 12 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hrawlen _)
      _ = _ := by rw [mul_pow]; ring
  have hf := structuralFormatterBudget_le r
  change structuralFormatterBudget r ≤ 4000000000 * S ^ 5 at hf
  have hp : S ^ 5 ≤ S ^ 12 := Nat.pow_le_pow_right hS (by decide)
  have hf' := hf.trans (Nat.mul_le_mul_left 4000000000 hp)
  have h0 : 1 ≤ S ^ 12 := Nat.pow_pos hS
  unfold structuralBudget
  change 4 * structuralFormatterBudget r + 4 * structuralRawBudget (structuralRawRequest r) + 12 ≤ _
  calc
    _ ≤ 4 * (4000000000 * S ^ 12) + 4 * (Kr * 33 ^ 12 * S ^ 12) + 12 * S ^ 12 := by omega
    _ = _ := by ring

end NearQuarticWires.StageMainMask
