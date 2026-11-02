import Proof.Quartic.StageModularCuts.SetupContract
import Proof.Quartic.StageModularCuts.Workspace

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the literal cold
setup state supplies the complete fixed-width coefficient workspace. -/
theorem ready_workspace (r : Setup.Request) : Workspace (Setup.ready r) r.fieldWidth r.modulus := by
  refine ⟨⟨0, 0, 0, 0, ?_⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_⟩
  · exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · change (frame (binary (r.fieldWidth + 1) 0)).length ≤ _
    rw [frame_length, SignedSortKey.binary_length]

/-- `prop:time`, paper/paper.tex: the scalar width
sum controls each finite binary and dense-coordinate width. -/
theorem setup_scale_bounds (r : Setup.Request) :
    2 ≤ Setup.scale r ∧ r.width + r.fieldWidth + 2 ≤ Setup.scale r := by
  unfold Setup.scale
  omega

/-- `prop:time`, paper/paper.tex: capacity is linear
in the actual row stream and dominates all source/output cursor advances. -/
theorem setup_capacity_lower (r : Setup.Request) :
    100 * Setup.scale r * (r.stream.length + 1) ≤ Setup.capacity r := by
  have hp : Setup.scale r ≤ (Setup.scale r) ^ 8 := Nat.le_self_pow (by decide) _
  have hc : 100 * Setup.scale r ≤ 10 ^ 8 * (Setup.scale r) ^ 8 := by nlinarith
  exact Nat.mul_le_mul_right (r.stream.length + 1) hc

/-- `prop:time`, paper/paper.tex: the real source
and framed output streams and dense stride all fit the fixed capacity. -/
theorem setup_stream_capacity (r : Setup.Request) :
    r.stream.length + 1 ≤ Setup.capacity r ∧
    2 * r.stream.length + 1 ≤ Setup.capacity r ∧
    2 * r.width + 1 ≤ Setup.capacity r := by
  have h := setup_capacity_lower r
  obtain ⟨hs, hw⟩ := setup_scale_bounds r
  have hm : Setup.scale r ≤ Setup.scale r * (r.stream.length + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  constructor
  · nlinarith
  constructor <;> nlinarith

end NearQuarticWires.StageModularCuts
