import Proof.Quartic.StageMainMask.StructuralScale

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageMain StageMain.Compact

/-- `prop:time`, paper/paper.tex: all fixed
machine dimensions and the header-width multiplier enter only the
constant in the shared structural arity bound. -/
noncomputable def structuralCoefficient (B1 B2 : ℕ) : ℕ :=
  (10 * (capacityCoefficient B1 + 3)) * 4 ^ capacityExponent B1 B2 +
    capacityExponent B1 B2 + TSK StageGamma.fieldProducerCallee + VV + MM + 1002

/-- `prop:time`, paper/paper.tex: the actual
binary-header workspace scale is polynomial in the original arity. -/
theorem structuralScale_polynomial (B1 B2 n : ℕ) :
    structuralScale B1 B2 n ≤ structuralCoefficient B1 B2 *
      (n + 1) ^ (capacityExponent B1 B2 + 1) := by
  have hw := StageMain.Runtime.header_power_le (10 * (capacityCoefficient B1 + 3))
    (capacityExponent B1 B2) n
  change (structuralSizes B1 B2).W (1 + natBitLength n) ≤
    (10 * (capacityCoefficient B1 + 3) * 4 ^ capacityExponent B1 B2) *
      (n + 1) ^ capacityExponent B1 B2 at hw
  have hp : (n + 1) ^ capacityExponent B1 B2 ≤
      (n + 1) ^ (capacityExponent B1 B2 + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (capacityExponent B1 B2 + 1) :=
    Nat.le_self_pow (by omega) _
  have h0 : 1 ≤ (n + 1) ^ (capacityExponent B1 B2 + 1) := Nat.pow_pos (Nat.succ_pos _)
  have hw' := hw.trans (Nat.mul_le_mul_left
    (10 * (capacityCoefficient B1 + 3) * 4 ^ capacityExponent B1 B2) hp)
  unfold structuralScale structuralCoefficient
  nlinarith

/-- `def:mask` and `prop:time`, paper/paper.tex: the shared cold structural endpoint has one fixed arity-only
polynomial budget for all actual selected calls, witnesses and pairs. -/
theorem structuralBudget_arity (B1 B2 : ℕ) :
    ∃ K d : ℕ, ∀ r : StructuralRequest B1 B2,
      structuralBudget r ≤ K * (r.call.n + 1) ^ d := by
  obtain ⟨K, hK⟩ := structuralBudget_scale
  refine ⟨K * structuralCoefficient B1 B2 ^ 12,
    (capacityExponent B1 B2 + 1) * 12, ?_⟩
  intro r
  calc
    _ ≤ K * (structuralScale B1 B2 r.call.n) ^ 12 := hK B1 B2 r
    _ ≤ K * (structuralCoefficient B1 B2 *
        (r.call.n + 1) ^ (capacityExponent B1 B2 + 1)) ^ 12 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (structuralScale_polynomial B1 B2 _) _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end NearQuarticWires.StageMainMask
