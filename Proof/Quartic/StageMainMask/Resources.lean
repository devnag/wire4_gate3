import Proof.Quartic.StageMainMask.NativeCost
import Proof.Quartic.StageMain.MainEntryBounds

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageMain

/-- `prop:time`, paper/paper.tex: a fixed
original-arity polynomial bounds the actual finite numeric-entry
source, including all retained parameter and witness records. -/
theorem entrySourceScale_arity (B1 B2 : ℕ) :
    ∃ K d : ℕ, ∀ r : EntryRequest B1 B2,
      entrySourceScale r ≤ K * (r.call.n + 1) ^ d := by
  refine ⟨20 * (7 * Bounds.coefficient B1 0 + 2), Bounds.degree B1 B2 0, ?_⟩
  intro r
  have h := Bounds.entry_word_le 0 0 r
  have hp : 1 ≤ (r.call.n + 1) ^ Bounds.degree B1 B2 0 := Nat.pow_pos (Nat.succ_pos _)
  unfold entrySourceScale Bounds.envelope at *
  nlinarith

/-- `prop:time`, paper/paper.tex: one finite
resource bound funds actual source and four-point work and all three
complete cold subroutines, including their fixed nested selectors. -/
noncomputable def entryResources {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  100000000 * (entrySourceScale r + 1) ^ 4 +
    1000000 * (structuralBudget (entryStructuralRequest r) +
      StageMainPopulation.populationBudget (entryPopulationRequest r) +
      framedPredicateBudget (entryPredicateRequest r).word.length + entrySourceScale r + 1)

/-- `prop:time`, paper/paper.tex: the whole
actual source, semantic original-point calculation and cold helper
budgets admit one fixed original-arity polynomial, uniformly over
all columns, samples, witnesses and complete original calls. -/
theorem entryResources_arity (B1 B2 : ℕ) :
    ∃ K d : ℕ, ∀ r : EntryRequest B1 B2,
      entryResources r ≤ K * (r.call.n + 1) ^ d := by
  obtain ⟨A, e, hA⟩ := entrySourceScale_arity B1 B2
  obtain ⟨Ks, es, hKs⟩ := structuralBudget_arity B1 B2
  obtain ⟨Kp, ep, hKp⟩ := StageMainPopulation.populationBudget_polynomial
  obtain ⟨Kv, ev, hKv⟩ := framedPredicateBudget_polynomial
  let D := es + ep * e + ev * e + 4 * e + e
  let K := 100000000 * (A + 1) ^ 4 +
    1000000 * (Ks + Kp * (A + 1) ^ ep + Kv * (A + 1) ^ ev + A + 1)
  refine ⟨K, D, ?_⟩
  intro r
  let X := r.call.n + 1
  have hX : 1 ≤ X := Nat.succ_pos _
  have h0 : 1 ≤ X ^ e := Nat.pow_pos hX
  have hS : entrySourceScale r + 1 ≤ (A + 1) * X ^ e := by
    have hh := hA r
    change entrySourceScale r ≤ A * X ^ e at hh
    nlinarith
  have hpow (k : ℕ) (hk : k * e ≤ D) :
      (entrySourceScale r + 1) ^ k ≤ (A + 1) ^ k * X ^ D := by
    calc
      _ ≤ ((A + 1) * X ^ e) ^ k := Nat.pow_le_pow_left hS k
      _ = (A + 1) ^ k * X ^ (k * e) := by rw [mul_pow, ← pow_mul, Nat.mul_comm e k]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk)
  have hword := entryRequest_words r
  have hpop : StageMainPopulation.populationBudget (entryPopulationRequest r) ≤
      (Kp * (A + 1) ^ ep) * X ^ D := by
    calc
      _ ≤ Kp * ((entryPopulationRequest r).word.length + 1) ^ ep := hKp _
      _ ≤ Kp * (entrySourceScale r + 1) ^ ep := by gcongr; exact hword.2.1
      _ ≤ Kp * ((A + 1) ^ ep * X ^ D) := Nat.mul_le_mul_left _ (hpow ep (by dsimp [D]; omega))
      _ = _ := by ring
  have hpred : framedPredicateBudget (entryPredicateRequest r).word.length ≤
      (Kv * (A + 1) ^ ev) * X ^ D := by
    calc
      _ ≤ Kv * ((entryPredicateRequest r).word.length + 1) ^ ev := hKv _
      _ ≤ Kv * (entrySourceScale r + 1) ^ ev := by gcongr; exact hword.2.2
      _ ≤ Kv * ((A + 1) ^ ev * X ^ D) := Nat.mul_le_mul_left _ (hpow ev (by dsimp [D]; omega))
      _ = _ := by ring
  have hstr : structuralBudget (entryStructuralRequest r) ≤ Ks * X ^ D :=
    (hKs _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by dsimp [D]; omega)))
  have hscale : entrySourceScale r + 1 ≤ (A + 1) * X ^ D := by
    exact hS.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by dsimp [D]; omega)))
  have hfour := hpow 4 (by dsimp [D]; omega)
  unfold entryResources
  change _ ≤ K * X ^ D
  calc
    _ ≤ 100000000 * ((A + 1) ^ 4 * X ^ D) +
        1000000 * (Ks * X ^ D + (Kp * (A + 1) ^ ep) * X ^ D +
          (Kv * (A + 1) ^ ev) * X ^ D + (A + 1) * X ^ D) := by omega
    _ = _ := by dsimp [K]; ring

end NearQuarticWires.StageMainMask
