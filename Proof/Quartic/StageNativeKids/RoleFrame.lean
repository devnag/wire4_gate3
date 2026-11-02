import Proof.Quartic.StageNativeKids.RoleValid
import Proof.Quartic.StageRecovery.OutputFrame

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open StageTuple

attribute [local irreducible] coldRoleProgram RolePacket.values RolePacket.outputValues
  RolePacket.widthBound RolePacket.steps

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual role reply is framed during the
real source computation, with every output marker charged. -/
noncomputable def roleFrameBudget (r : RoleRequest) : ℕ :=
  langBudget StageRecovery.packetCallee roleSizes VV MM r.word (3 * r.steps + 2)

/-- `lem:print`, paper/paper.tex: the
actual role program writes one outer marker for each emitted reply bit
and its final delimiter, with the original role semantics unchanged. -/
theorem roleFrame_spec (C : Ctx) (r : RoleRequest)
    (hin : C.inp = r.word) (hwidth : r.packet.widthBound ≤ C.Wd) :
    Hs C (StageRecovery.OutputFrame.framedProgram coldRoleProgram)
      (a0 : DS VV MM) (3 * r.steps + 2) (fun b => b.out = frame r.packet.output) := by
  obtain ⟨b, n, he, hn, ho⟩ := coldRoleProgram_spec C r hin hwidth
  have hf := StageRecovery.OutputFrame.framedProgram_spec he
  have hz : StageRecovery.OutputFrame.markedState (a0 : DS VV MM) = a0 := rfl
  rw [hz] at hf
  refine ⟨StageRecovery.OutputFrame.framedState b, 3 * n + 2, hf, by omega, ?_⟩
  change frame b.out = frame r.packet.output
  rw [ho]

/-- `lem:print`, paper/paper.tex: the
complete ordinary role machine writes its original occurrence and
exact affine row header in one physical measured frame. -/
noncomputable def roleFrameWordFunction :
    WordFunction RoleRequest RoleRequest.word (fun r => frame r.packet.output) roleFrameBudget :=
  wordFunction_of_lang RoleRequest.word (fun r => frame r.packet.output)
    StageRecovery.packetCallee roleSizes
    (StageRecovery.OutputFrame.framedProgram coldRoleProgram)
    (fun r => 3 * r.steps + 2) (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := roleFrame_spec
        (ctxOf StageRecovery.packetCallee roleSizes r.word) r rfl r.context_width
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := r.context_width
      have h0 : 1 ≤ r.packet.widthBound := by
        unfold RolePacket.widthBound
        have hh : 0 < (r.packet.scalars 0 + 1) ^ 4 := Nat.pow_pos (by omega)
        omega
      exact h0.trans h)

/-- `lem:print` and `prop:time`, paper/paper.tex: each actual source atom pays the exact
framed role computation with its validity bounds already derived. -/
noncomputable def framedRoleBudget (r : NativeKidsRequest) : ℕ :=
  roleFrameBudget (actualRoleRequest r.toRowContext r.atom)

/-- `lem:print`, paper/paper.tex: no valid
role request is supplied by the native caller; the actual source atom
and original metadata determine the complete framed reply. -/
noncomputable def framedRoleWordFunction :
    WordFunction NativeKidsRequest
      (fun r => (r.toRowContext.rolePacket r.atom).word)
      (fun r => frame (natWord (r.toRowContext.originalIndex r.atom).val ++
        r.toRowContext.rowHeader r.atom)) framedRoleBudget :=
  ⟨roleFrameWordFunction.program, by
    intro r
    simpa only [RoleRequest.word, actualRoleRequest, role_output, framedRoleBudget]
      using roleFrameWordFunction.realizes (actualRoleRequest r.toRowContext r.atom)⟩

end NearQuarticWires.StageNativeKids
