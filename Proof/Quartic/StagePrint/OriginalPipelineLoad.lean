import Proof.Quartic.StagePrint.OriginalPipelineLoadBase

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

attribute [local irreducible] firstTapes selectTapes pullTapes

/-- `lem:print`, paper/paper.tex: the eleven actual input fields are physically extracted before any child compilation or row selection. -/
theorem originalPipelineLoad_spec {second : Bool} (cap : ℕ) (r : OriginalPipelineRequest second) :
    WXExec cap (.mach Top.loadM (pipelineLoadMap second))
      (idealStart (pipelineStreams second) 3 r.word r.lens) r.loaded r.loadCost := by
  have ld:=Top.load_run (frame r.source.source) (frame (List.replicate r.row.compilerIndex.val true))
    (frame (r.row.header r.row.fields_fit)) [] [] [] [] [] [] [] [] r.loadCapacity
    (by unfold OriginalPipelineRequest.loadCapacity OriginalPipelineRequest.word;omega)
    (by unfold OriginalPipelineRequest.loadCapacity;omega)
  obtain ⟨actual,hr,hh,ht,_⟩:=ld
  let σ:=idealStart (pipelineStreams second) 3 r.word r.lens
  have hin : (fun j : Fin 14=>σ.st (pipelineLoadMap second j))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.loadCapacity false) := by
    funext j
    refine Fin.addCases (motive:=fun j=>σ.st (pipelineLoadMap second j)=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.loadCapacity false) j)
      (fun i : Fin 13=>?_) (fun i : Fin 1=>?_) j
    · rw [Fin.addCases_left,pipeline_initial_fields]
      have hz:=r.lens_small (pipelineLoadMap second (Fin.castAdd 1 i)) i.isLt
      change (if i.val=0 then frame r.word else
        List.replicate (r.lens (pipelineLoadMap second (Fin.castAdd 1 i))) false)=_
      rw [hz,List.replicate_zero]
    · rw [Fin.addCases_right]
      have hi : i=0:=Fin.eq_zero i
      subst hi
      simp [σ,idealStart,pipelineLoadMap,OriginalPipelineRequest.lens]
  change run Top.loadM r.loadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate r.loadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨τ,e,dock⟩:=WXExec.mach_run cap (pipelineMap_injective second).2.2.2 σ (fun _=>rfl) hr
  have heq : τ=r.loaded := by
    apply WState.eq
    · funext i
      by_cases hi : i.val<14
      · let j : Fin 14:=⟨i.val,hi⟩
        have hij : pipelineLoadMap second j=i:=Fin.ext rfl
        rw [←hij,dock.sh,hh]
        rfl
      · rw [(dock.other i (by intro j h;have hv:=congrArg Fin.val h;have:=j.isLt;simp only [pipelineLoadMap,Fin.val_mk] at hv;omega)).2]
        rfl
    · funext i
      by_cases hi : i.val<14
      · let j : Fin 14:=⟨i.val,hi⟩
        have hij : pipelineLoadMap second j=i:=Fin.ext rfl
        rw [←hij,dock.st,ht]
        change Fin.addCases r.fields (fun _ : Fin 1=>List.replicate r.loadCapacity false) j=
          r.loaded.st (pipelineLoadMap second j)
        exact (r.loaded_field j).symm
      · rw [(dock.other i (by intro j h;have hv:=congrArg Fin.val h;have:=j.isLt;simp only [pipelineLoadMap,Fin.val_mk] at hv;omega)).1]
        simp [σ,idealStart,OriginalPipelineRequest.loaded,show ¬i.val<13 by omega,
          show i.val≠0 by omega,show i≠0 by intro h;have hv:=congrArg Fin.val h;simp only [Fin.val_zero] at hv;omega]
    · exact dock.val
    · exact dock.cell
  exact e.cast cap heq le_rfl

end NearQuarticWires.StagePrint
