import Proof.Quartic.StageNativeKids.SourceLayout
import Proof.Quartic.StageNativeKids.RoleFrame
import Proof.Quartic.Control.Frame

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open StageTuple StagePrint.Header

attribute [local irreducible] framedRoleWordFunction

local notation "t" => framedRoleWordFunction.program.tapeCount

/-- `lem:print`, paper/paper.tex: the
source stage first loads the actual eleven fields, constructs the actual
role packet and invokes the concrete ordinary role machine once. -/
noncomputable def sourceRoleProgram : WMX (t + 15) 3 :=
  .seq (.mach Top.loadM (sourceLoadMap t))
    (.seq (.wm (roleSourceReadyProgram (sourceRoleSources t) 0 1 2))
      (.machZ framedRoleWordFunction.program.machine (sourceRoleMap t) (sourceRoleRuler t)))

/-- `prop:time`, paper/paper.tex: actual
source loading, exact binary request formatting and the once-only
ordinary role computation all contribute to the source clock. -/
noncomputable def sourceRoleClock (r : NativeKidsRequest) : ℕ :=
  r.sourceLoadCost + roleSourceReadyCost ((baseHeaderValues r.header).flatMap natWord)
    [r.header.call.first.gates.length, r.header.call.second.gates.length,
      r.header.prepared.seedParameters.N, r.walkCode.val] r.atom.val +
    2 * framedRoleBudget r + 4

/-- `lem:print` and `prop:time`, paper/paper.tex: wholly cold original source and blank work
tapes produce the real framed role reply. Every original field remains
retained, with zero source heads, for actual subsequent bank and child
selection; no decoded occurrence or row is an input. -/
theorem sourceRole_run (cap : ℕ) (r : NativeKidsRequest) (σ : WState (t + 15) 3)
    (hin : (fun j : Fin 14 => σ.st (sourceLoadMap t j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.sourceLoadCapacity false))
    (hh : ∀ j : Fin 14, σ.sh (sourceLoadMap t j) = 0)
    (hb : ∀ j : Fin t, σ.st (sourceRoleMap t j) = [])
    (hbh : ∀ j : Fin t, σ.sh (sourceRoleMap t j) = 0)
    (hR : σ.st (sourceRoleRuler t) = List.replicate (framedRoleBudget r) false)
    (hRh : σ.sh (sourceRoleRuler t) = 0) (hz : ∀ j, σ.val j = 0)
    (hcap : 2 * (((baseHeaderValues r.header).flatMap natWord).length +
      ([r.header.call.first.gates.length, r.header.call.second.gates.length,
        r.header.prepared.seedParameters.N, r.walkCode.val].flatMap natWord).length +
      (natWord r.atom.val).length) + 3 ≤ cap) :
    ∃ τ, WXExec cap sourceRoleProgram σ τ (sourceRoleClock r) ∧
      τ.st (sourceRoleMap t framedRoleWordFunction.program.outputTape) =
        frame (natWord (r.toRowContext.originalIndex r.atom).val ++
          r.toRowContext.rowHeader r.atom) ∧
      (∀ j : Fin 13, τ.st (sourceLoadMap t (Fin.castAdd 1 j)) = r.loadedSource j) ∧
      (∀ j : Fin 13, τ.sh (sourceLoadMap t (Fin.castAdd 1 j)) = 0) ∧
      (∀ j : Fin t, τ.sh (sourceRoleMap t j) = 0) ∧
      (∀ i, (∀ j, sourceLoadMap t j ≠ i) → (∀ j, sourceRoleMap t j ≠ i) →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      τ.val = σ.val := by
  obtain ⟨loaded, eload, hl, hlh, hlv, _hlc⟩ :=
    sourceLoad_run cap r (sourceLoadMap t) (sourceLoadMap_injective t) σ hin hh
  have loaded_off (i : Fin (t + 16)) (hi : ∀ j, sourceLoadMap t j ≠ i) :
      loaded.st i = σ.st i ∧ loaded.sh i = σ.sh i :=
    NearQuarticWires.Control.WXExec.avoids eload hi
  have role_off (j : Fin t) : loaded.st (sourceRoleMap t j) = [] ∧
      loaded.sh (sourceRoleMap t j) = 0 := by
    have h := loaded_off (sourceRoleMap t j) (fun k => (sourceRoleMap_off t j k).symm)
    exact ⟨h.1.trans (hb j), h.2.trans (hbh j)⟩
  have ruler_off : loaded.st (sourceRoleRuler t) = σ.st (sourceRoleRuler t) ∧
      loaded.sh (sourceRoleRuler t) = σ.sh (sourceRoleRuler t) := by
    apply loaded_off
    intro j h
    have he := congrArg Fin.val h
    change j.val = 14 + t at he
    omega
  have hwrite := roleSourceReadyProgram_spec cap (sourceRoleSources t) (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) ((baseHeaderValues r.header).flatMap natWord)
    [r.header.call.first.gates.length, r.header.call.second.gates.length,
      r.header.prepared.seedParameters.N, r.walkCode.val] r.atom.val rfl [] [] [] loaded
    (by simpa [NativeKidsRequest.loadedSource, NativeKidsRequest.sourceFields,
        sourceLoadMap, sourceRoleSources] using hl ⟨3, by decide⟩)
    (by simpa [NativeKidsRequest.loadedSource, NativeKidsRequest.sourceFields,
        NativeKidsRequest.contextWord, sourceLoadMap, sourceRoleSources] using hl ⟨4, by decide⟩)
    (by simpa [NativeKidsRequest.loadedSource, NativeKidsRequest.sourceFields,
        sourceLoadMap, sourceRoleSources] using hl ⟨5, by decide⟩)
    (by intro j; fin_cases j
        · exact hlh 3
        · exact hlh 4
        · exact hlh 5
        · exact (role_off (tape0 framedRoleWordFunction.program)).2)
    ((role_off (tape0 framedRoleWordFunction.program)).1)
    (by rw [hlv]; exact hz 0) (by rw [hlv]; exact hz 1) (by rw [hlv]; exact hz 2) hcap
  have hword : (baseHeaderValues r.header).flatMap natWord ++
      [r.header.call.first.gates.length, r.header.call.second.gates.length,
        r.header.prepared.seedParameters.N, r.walkCode.val].flatMap natWord ++ natWord r.atom.val =
      (r.toRowContext.rolePacket r.atom).word := by
    rw [r.toRowContext.rolePacket_word]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rw [hword, sourceRoleSources_input] at hwrite
  let ready := loaded.sets (sourceRoleMap t (tape0 framedRoleWordFunction.program))
    (frame (r.toRowContext.rolePacket r.atom).word)
  obtain ⟨τ, ecall, hout, hheads, hoff, hval⟩ := wfDock_exact
    framedRoleWordFunction r cap (sourceRoleMap t) (sourceRoleMap_injective t)
    (sourceRoleRuler t) (sourceRoleMap_ruler t) ready
    (by simp [ready])
    (by intro j hj; simp [ready, (sourceRoleMap_injective t).ne hj, (role_off j).1])
    (by intro j; exact (role_off j).2) (framedRoleBudget r)
    (by simp [ready, (sourceRoleMap_ruler t _).symm, ruler_off.1, hR])
    (by exact ruler_off.2.trans hRh) le_rfl
  refine ⟨τ, (WXExec.seq eload (WXExec.seq (WXExec.wm hwrite) ecall)).mono
    (by unfold sourceRoleClock; omega), hout, ?_, ?_, hheads, ?_, hval.trans hlv⟩
  · intro j
    rw [(hoff _ (fun k => sourceRoleMap_off t k (Fin.castAdd 1 j))).1]
    simp only [ready, WState.sets_st,
      Function.update_of_ne (sourceRoleMap_off t _ (Fin.castAdd 1 j)).symm]
    exact hl j
  · intro j
    exact (hoff _ (fun k => sourceRoleMap_off t k (Fin.castAdd 1 j))).2.trans
      (hlh (Fin.castAdd 1 j))
  · intro i hload hrole
    obtain ⟨hst, hsh⟩ := hoff i hrole
    have he := loaded_off i hload
    constructor
    · rw [hst]
      simpa [ready, (hrole (tape0 framedRoleWordFunction.program)).symm] using he.1
    · exact hsh.trans he.2

end NearQuarticWires.StageNativeKids
