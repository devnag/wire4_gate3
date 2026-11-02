import Proof.Quartic.Cells.ParametersOutputCapacityPrinting
import Proof.Quartic.StageOutput.Preservation

/-!
# Numerical capacity for the complete Step 5 arithmetic

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The bounds depend only on the parsed numerical values.
A finite environment records those values and the mathematical powers for
the expression estimates; the execution constructs the powers separately.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def capacityEnvironment (d : Input) : Fin VV → ℕ :=
  Function.update (Function.update (Function.update (fieldEnv d.fields (fun _ => 0))
    powerN (2 ^ d.n)) powerK (2 ^ d.k)) roundD d.denominator

theorem capacityEnvironment_stored (d : Input) : d.Stored (capacityEnvironment d) := by
  apply d.stored_congr (d.fields_stored (fun _ => 0))
  intro x hx
  have hne : x ≠ roundD ∧ x ≠ powerK ∧ x ≠ powerN := by
    simp only [inputVariables, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [capacityEnvironment, Function.update_of_ne hne.1,
    Function.update_of_ne hne.2.1, Function.update_of_ne hne.2.2]

theorem arithmetic_capacity (d : Input) (B W : ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hn : d.n ≤ B) (hk : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ W) :
    d.floorValue.natAbs + d.ceilValue.natAbs + 2 ^ (d.n + 1) + 2 < 2 ^ W ∧
      d.centerNumerator ≤ 2 ^ (28 * (B + 1) + 2) ∧
      d.radiusNumerator ≤ 2 ^ (28 * (B + 1) + 2) ∧
      2 ^ (d.n + 1) ≤ 2 ^ (28 * (B + 1) + 2) ∧
      2 * 2 ^ (28 * (B + 1) + 2) ≤ 2 ^ W := by
  exact Cells.output_printing_capacity d B W (capacityEnvironment d) hf hn hk hw
    (capacityEnvironment_stored d)
    (by simp (config := { decide := true }) [capacityEnvironment])
    (by simp (config := { decide := true }) [capacityEnvironment])
    (by simp [capacityEnvironment])

end NearQuarticWires.StageOutput
