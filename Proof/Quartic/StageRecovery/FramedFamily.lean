import Proof.Quartic.StageRecovery.FamilyFrame
import Proof.Quartic.StageRecovery.FamilyCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: a complete native
family packet is physically supplied in one exact outer frame, including
its final record-stream delimiter, for ordinary-machine composition. -/
noncomputable def framedFamilyWordFunction :
    WordFunction FamilyRequest FamilyRequest.word (fun r => frame r.output)
      (fun r => 2 * familyFrameSteps r + 2) :=
  wordFunction_of_ideal familyFrameProgram familyFrameOut
    (by have h : 2 ≤ familyFrameTapes := familyWordFunction.program.twoTapes
        change familyFrameTapes ≠ 0
        omega)
    (fun r => 2 * r.output.length + 2) familyFrameLens familyFrameSteps
    (fun _ => le_rfl) (by
      intro r
      refine ⟨?_, familyFrameProgram_run r⟩
      unfold familyFrameLens
      rw [if_neg]
      intro h
      have hh := congrArg Fin.val h
      change familyFrameTapes = familyFrameTapes + 1 at hh
      omega)

/-- `prop:time`, paper/paper.tex: the exact length of
the actual generated packet includes one terminal record-stream bit. -/
theorem FamilyRequest.output_length (r : FamilyRequest) :
    r.output.length = (fam r.arity r.degree).length * (2 * r.width + 1) + 1 := by
  simp [FamilyRequest.output, NearCubicGates.Close.WordPrograms.recStream, List.length_flatMap,
    frame_length, SignedSortKey.binary_length, famRecs_length, Function.comp_def]

/-- `prop:time`, paper/paper.tex: native generation and
outer framing together retain one linear factor of support-family size. -/
theorem framedFamilyBudget_le (r : FamilyRequest) :
    2 * familyFrameSteps r + 2 ≤
      10 ^ 10 * ((fam r.arity r.degree).length + 1) * (r.arity + r.degree + 9) ^ 4 := by
  have hb := r.budget_le
  have hH : 1 ≤ r.arity + r.degree + 9 := by omega
  have hH4 : r.arity + r.degree + 9 ≤ (r.arity + r.degree + 9) ^ 4 := by
    exact Nat.le_self_pow (by norm_num) _
  have hN : 1 ≤ (fam r.arity r.degree).length + 1 := by omega
  have hprod := Nat.mul_le_mul_left ((fam r.arity r.degree).length + 1) hH4
  have hprod1 := Nat.mul_le_mul_right ((r.arity + r.degree + 9) ^ 4) hN
  unfold familyFrameSteps
  rw [r.output_length]
  unfold FamilyRequest.width
  nlinarith

end NearQuarticWires.StageRecovery
