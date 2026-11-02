import Proof.Quartic.StageNativeKids.AcquireInitial

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StageTuple StagePrint.Header

attribute [local irreducible] framedRoleWordFunction sourceRoleProgram sourceRoleClock
  acquireFormatProgram acquireFormatCost
local notation "t" => framedRoleWordFunction.program.tapeCount

/-- `lem:print` and `prop:time`, paper/paper.tex: the source-to-role computation and real
formatter run from the actual cold original request, produce the exact
next source record, and charge all acquisition, call and output work. -/
theorem acquire_run (r : NativeKidsRequest) :
    ∃ τ, WXExec (acquireCapacity r) acquireProgram
      (idealStart (t + 15) 3 r.word (acquireLens r)) τ (acquireClock r) ∧
      τ.st (acquireOutput t) = frame r.acquiredWord := by
  let σ := acquireStart r
  have hroleCap : 2 * (((baseHeaderValues r.header).flatMap natWord).length +
      ([r.header.call.first.gates.length, r.header.call.second.gates.length,
        r.header.prepared.seedParameters.N, r.walkCode.val].flatMap natWord).length +
      (natWord r.atom.val).length) + 3 ≤ acquireCapacity r := by
    have hw := congrArg List.length (r.toRowContext.rolePacket_word r.atom)
    simp only [List.length_append] at hw
    unfold acquireCapacity
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
    omega
  obtain ⟨a, erole, hrole, hsource, hsourceHead, hroleHead, hoff, hval⟩ :=
    sourceRole_run (acquireCapacity r) r σ (acquireStart_source r) (fun _ => rfl)
      (acquireStart_roleBlank r) (fun _ => rfl)
      (acquireStart_ruler r) rfl (fun _ => rfl) hroleCap
  have hfinal := hoff (acquireOutput t)
    (by intro j h; have he := congrArg Fin.val h
        change j.val = 15 + t at he; omega)
    (by intro j h; have he := congrArg Fin.val h
        change 14 + j.val = 15 + t at he; omega)
  have hfinal0 : σ.st (acquireOutput t) = [] := acquireStart_output r
  have hformatCap : 2 * (r.prefixFields.flatMap frame).length +
      2 * (frame r.rolePayload).length + 30 ≤ acquireCapacity r := by
    have hw := congrArg List.length (source_prefix r)
    simp only [List.length_append, List.length_replicate] at hw
    unfold acquireCapacity
    have hf := NearCubicWires.RepairOrdinary.frame_length r.rolePayload
    omega
  have eformat := acquireFormatProgram_spec (acquireCapacity r)
    (acquireSources framedRoleWordFunction.program) (0 : Fin 3) 1 (by decide) r a
    (by change a.st (sourceLoadMap t 1) = r.word; exact hsource ⟨1, by decide⟩)
    hrole
    (by intro j; fin_cases j
        · exact hsourceHead ⟨1, by decide⟩
        · exact hroleHead _
        · exact hfinal.2)
    (hfinal.1.trans hfinal0) (by rw [hval]; rfl) (by rw [hval]; rfl) hformatCap
  refine ⟨_, (WXExec.seq erole (WXExec.wm eformat)).mono
    (by unfold acquireClock; omega), ?_⟩
  change (appendO a (acquireOutput t) 0 (frame r.acquiredWord)).st (acquireOutput t) = _
  rw [appendO_st, Function.update_self, hfinal.1, hfinal0, List.nil_append]

end NearQuarticWires.StageNativeKids
