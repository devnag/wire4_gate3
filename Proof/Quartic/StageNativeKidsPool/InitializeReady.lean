import Proof.Quartic.StageNativeKidsPool.Initialize

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
computed-count initialization establishes the real reusable-row loop
invariant with the actual finite source and affine header retained. -/
theorem initialized_ready (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (σ : WState (streams counter row) 16)
    (h : Counted F width countBudget counter row q σ) :
    Ready (rowLayout counter row) (F q).source (F q).header 0 (F q).count
      (initialized counter row (F q).count (width q) σ) := by
  have rowOut (j : Fin row.tapeCount) : rowMap counter row j≠
      (⟨14,by unfold streams;omega⟩ : Fin (streams counter row+1)):=by
    intro he;have hv:=congrArg Fin.val he;change 20+counter.tapeCount+j.val=14 at hv;omega
  have rowCount (j : Fin row.tapeCount) : rowMap counter row j≠
      counterMap counter row counter.outputTape:=(counterMap_ne_rowMap _ _ _ j).symm
  have smallCount (i : Fin (streams counter row+1)) (hi:i.val<20) :
      i≠counterMap counter row counter.outputTape:=(counterMap_not_small _ _ _ i hi).symm
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j
    change (initialized counter row (F q).count (width q) σ).st (rowMap counter row j)=[]
    simpa only [initialized,appendO,WState.setv_st,WState.seth_st,WState.sets_st,
      Function.update_of_ne (rowOut j)] using (h.row_bank j).1
  · intro j
    change (initialized counter row (F q).count (width q) σ).sh (rowMap counter row j)=0
    simpa only [initialized,appendO,WState.setv_sh,WState.seth_sh,WState.sets_sh,
      Function.update_of_ne (rowOut j),Function.update_of_ne (rowCount j)] using (h.row_bank j).2
  · have hh:=(h.small ⟨17,by unfold streams;omega⟩ (by change 17<20;omega)).1
    change (initialized counter row (F q).count (width q) σ).st ⟨17,by unfold streams;omega⟩=[]
    simpa [initialized,appendO,loaded,lens] using hh
  · have hh:=(h.small ⟨17,by unfold streams;omega⟩ (by change 17<20;omega)).2
    change (initialized counter row (F q).count (width q) σ).sh ⟨17,by unfold streams;omega⟩=0
    simpa [initialized,appendO,Function.update_of_ne
      (smallCount ⟨17,by unfold streams;omega⟩ (by change 17<20;omega))] using hh
  · have hh:=(h.small ⟨18,by unfold streams;omega⟩ (by change 18<20;omega)).1
    change (initialized counter row (F q).count (width q) σ).st ⟨18,by unfold streams;omega⟩=[]
    simpa [initialized,appendO,loaded,lens] using hh
  · have hh:=(h.small ⟨18,by unfold streams;omega⟩ (by change 18<20;omega)).2
    change (initialized counter row (F q).count (width q) σ).sh ⟨18,by unfold streams;omega⟩=0
    simpa [initialized,appendO,Function.update_of_ne
      (smallCount ⟨18,by unfold streams;omega⟩ (by change 18<20;omega))] using hh
  · have hh:=(h.small ⟨19,by unfold streams;omega⟩ (by change 19<20;omega)).1
    change Worker.Blank ((initialized counter row (F q).count (width q) σ).st ⟨19,by unfold streams;omega⟩)
    have hz : (initialized counter row (F q).count (width q) σ).st ⟨19,by unfold streams;omega⟩=[]:=by
      simpa [initialized,appendO,loaded,lens] using hh
    rw [hz]
    exact Control.nil_blank
  · have hh:=(h.small ⟨19,by unfold streams;omega⟩ (by change 19<20;omega)).2
    change (initialized counter row (F q).count (width q) σ).sh ⟨19,by unfold streams;omega⟩=0
    simpa [initialized,appendO,Function.update_of_ne
      (smallCount ⟨19,by unfold streams;omega⟩ (by change 19<20;omega))] using hh
  · intro i
    change (initialized counter row (F q).count (width q) σ).val (callRegisters i)=0
    fin_cases i <;> simp [callRegisters,initialized,appendO,h.registers]
  · change (initialized counter row (F q).count (width q) σ).val (4 : Fin 16)=0
    simp [initialized,appendO,h.registers]
  · intro i hi
    change (initialized counter row (F q).count (width q) σ).val (rowRegisters i)=0
    fin_cases i <;> first | exact False.elim (hi rfl) | simp [rowRegisters,initialized,appendO,h.registers]
  · have hh:=(h.small ⟨2,by unfold streams;omega⟩ (by change 2<20;omega)).1
    change (initialized counter row (F q).count (width q) σ).st ⟨2,by unfold streams;omega⟩=frame (F q).source
    simpa [initialized,appendO,loaded,fields] using hh
  · have hh:=(h.small ⟨3,by unfold streams;omega⟩ (by change 3<20;omega)).1
    change (initialized counter row (F q).count (width q) σ).st ⟨3,by unfold streams;omega⟩=frame (F q).header
    simpa [initialized,appendO,loaded,fields] using hh
  · intro i
    fin_cases i
    · have hh:=(h.small ⟨2,by unfold streams;omega⟩ (by change 2<20;omega)).2
      simpa [rowLayout,rowSources,initialized,appendO,Function.update_of_ne
        (smallCount ⟨2,by unfold streams;omega⟩ (by change 2<20;omega))] using hh
    · have hh:=(h.small ⟨3,by unfold streams;omega⟩ (by change 3<20;omega)).2
      simpa [rowLayout,rowSources,initialized,appendO,Function.update_of_ne
        (smallCount ⟨3,by unfold streams;omega⟩ (by change 3<20;omega))] using hh
    · simpa [rowLayout,rowSources,rowSite,Control.Site.input] using
        (show (initialized counter row (F q).count (width q) σ).sh
          (rowMap counter row (WorkerArith.inTape row))=0 from by
          simpa only [initialized,appendO,WState.setv_sh,WState.seth_sh,WState.sets_sh,
            Function.update_of_ne (rowOut _),Function.update_of_ne (rowCount _)] using
              (h.row_bank (WorkerArith.inTape row)).2)
  · have hs:=(h.small ⟨14,by unfold streams;omega⟩ (by change 14<20;omega))
    have hz : σ.st (⟨14,by unfold streams;omega⟩ : Fin (streams counter row+1))=[]:=by
      simpa [loaded,lens] using hs.1
    change (initialized counter row (F q).count (width q) σ).sh ⟨14,by unfold streams;omega⟩=
      ((initialized counter row (F q).count (width q) σ).st ⟨14,by unfold streams;omega⟩).length
    simp [initialized,appendO,Function.update_of_ne
      (smallCount ⟨14,by unfold streams;omega⟩ (by change 14<20;omega)),hs.2,hz]
  · change (initialized counter row (F q).count (width q) σ).val (9 : Fin 16)=(F q).count
    simp [initialized]

end NearQuarticWires.StageNativeKidsPool
