import Proof.Quartic.StageTupleSetupCold.Program

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StageTuple

namespace Helpers

/-- `lem:print`, paper/paper.tex: two
distinct retained-data slots name distinct physical tapes. -/
theorem data_ne (F : Helpers) {i j : Fin 24} (h : i≠j) : F.data i≠F.data j :=
  StageTupleSetup.BankLayout.dataTape_injective.ne h

/-- `lem:print`, paper/paper.tex: the
original loader bank excludes every later cache, output and ruler. -/
theorem loader_ne_data (F : Helpers) (j : Fin 14) (i : Fin 24) (hi : 14 ≤ i.val) :
    F.loader j≠F.data i := by
  intro h
  have hv:=congrArg Fin.val h
  change j.val=i.val at hv
  have hj:=j.isLt
  omega

/-- `lem:print`, paper/paper.tex: the
actual cold prelude acquires all original fields and physically frames
the independent context/degree codecs. Every helper bank stays cold;
no helper reply, decoded count or supplied context cache is assumed. -/
theorem prelude_run (F : Helpers) (r : TermCutRequest) :
    ∃σ,WXExec (capacity r) F.prelude (F.initial r) σ
      (r.sourceLoadCost+1+(1000*(r.contextWord.length+1)+1+
        1000*((natWord r.degree).length+1))) ∧
      Ready F r σ ∧
      ∀i,(∀j : Fin 24,i≠F.data j)→σ.st i=[] := by
  obtain ⟨a,tout,eload,hd,hl,hh,hz⟩:=F.load_ready r
  have hcache (i : Fin 24) (hi : 14 ≤ i.val) : a.st (F.data i)=(F.initial r).st (F.data i) :=
    (hd.other (F.data i) (fun j=>F.loader_ne_data j i hi)).1
  have hfree : ∀i,(∀j : Fin 24,i≠F.data j)→a.st i=[] := by
    intro i hi
    exact ((hd.other i (fun j=>(hi ⟨j.val,by have hj:=j.isLt;omega⟩).symm)).1).trans
      (F.initial_other r i hi)
  let values : List ℕ :=[r.header.call.first.gates.length,r.header.call.second.gates.length,
    r.header.prepared.seedParameters.N,r.walkCode.val]
  have hv : values.flatMap natWord=r.contextWord :=by
    simp [values,TermCutRequest.contextWord,List.append_assoc]
  have ec:=StageTuple.contextFrameProgram_spec (capacity r) F.contextPair (regs 3 (by decide))
    values rfl a (by rw [hv];exact hl 4) (hh _)
    ((hcache 14 (by decide)).trans rfl) (hh _) (fun _=>hz _) (by rw [hv];unfold capacity;omega)
  rw [hv] at ec
  let b:=a.sets (F.data 14) (frame r.contextWord)
  have hb : ∀i,b.sh i=0 :=hh
  have bz : ∀i,b.val i=0 :=hz
  have ed:=StageTupleSetup.frameNaturalProgram_spec (capacity r) F.degreePair (regs 3 (by decide))
    r.degree b (by
      change (a.sets (F.data 14) (frame r.contextWord)).st (F.data 7)=_
      rw [WState.sets_st,Function.update_of_ne (F.data_ne (by decide : (7 : Fin 24)≠14))]
      exact hl 7) (hb _) (by
      change (a.sets (F.data 14) (frame r.contextWord)).st (F.data 15)=[]
      rw [WState.sets_st,Function.update_of_ne (F.data_ne (by decide : (15 : Fin 24)≠14))]
      exact (hcache 15 (by decide)).trans rfl) (hb _) (fun _=>bz _) (by unfold capacity;omega)
  let c:=b.sets (F.data 15) (frame (natWord r.degree))
  have hkeep (i : Fin 24) (hi14 : i≠14) (hi15 : i≠15) : c.st (F.data i)=a.st (F.data i) :=by
    change ((a.sets (F.data 14) _).sets (F.data 15) _).st _=_
    rw [WState.sets_st,Function.update_of_ne (F.data_ne hi15),
      WState.sets_st,Function.update_of_ne (F.data_ne hi14)]
  refine ⟨c,eload.seq ((WXExec.wm ec).seq (WXExec.wm ed)),?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hh,hz⟩
    · intro j
      have hj:=j.isLt
      exact (hkeep ⟨j.val,by omega⟩ (by intro h;have hv:=congrArg Fin.val h;norm_num at hv;omega)
        (by intro h;have hv:=congrArg Fin.val h;norm_num at hv;omega)).trans (hl j)
    · change ((a.sets (F.data 14) _).sets (F.data 15) _).st (F.data 14)=_
      rw [WState.sets_st,Function.update_of_ne (F.data_ne (by decide : (14 : Fin 24)≠15)),
        WState.sets_st,Function.update_self]
    · change ((a.sets (F.data 14) _).sets (F.data 15) _).st (F.data 15)=_
      rw [WState.sets_st,Function.update_self]
    · exact (hkeep 16 (by decide) (by decide)).trans ((hcache 16 (by decide)).trans rfl)
    · exact (hkeep 20 (by decide) (by decide)).trans ((hcache 20 (by decide)).trans rfl)
    · exact (hkeep 21 (by decide) (by decide)).trans ((hcache 21 (by decide)).trans rfl)
    · exact (hkeep 22 (by decide) (by decide)).trans ((hcache 22 (by decide)).trans rfl)
    · exact (hkeep 23 (by decide) (by decide)).trans ((hcache 23 (by decide)).trans rfl)
  · intro i hi
    change ((a.sets (F.data 14) _).sets (F.data 15) _).st i=[]
    rw [WState.sets_st,Function.update_of_ne (hi 15),WState.sets_st,Function.update_of_ne (hi 14)]
    exact hfree i hi

end Helpers

end NearQuarticWires.StageTupleSetupCold
