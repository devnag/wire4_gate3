import Proof.Quartic.StagePrint.RawColdMachine
import Proof.Gates.CounterAsm.Copy
import Proof.Gates.TabMachine.Occ

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the original-child machine's complete fixed tape bank. -/
noncomputable abbrev childFrameTapes : ℕ := originalChildPrinter.program.tapeCount

/-- `lem:print`, paper/paper.tex: the child machine uses the initial bank without sharing its work tapes with the record framer. -/
def childFrameMap (j : Fin childFrameTapes) : Fin (childFrameTapes+2) := ⟨j.val,by omega⟩

/-- `lem:print`, paper/paper.tex: the exact original-child stream is the subsequent physical framer's source. -/
noncomputable def childFrameSource : Fin (childFrameTapes+2) :=
  childFrameMap originalChildPrinter.program.outputTape

/-- `lem:print`, paper/paper.tex: a fresh tape stores the outer frame around all original children. -/
noncomputable def childFrameOut : Fin (childFrameTapes+2) := ⟨childFrameTapes,by omega⟩

/-- `lem:print`, paper/paper.tex: the finite run ruler is separate from both the child bank and its framed output. -/
noncomputable def childFrameRuler : Fin (childFrameTapes+2) := ⟨childFrameTapes+1,by omega⟩

/-- `lem:print`, paper/paper.tex: every child record contains its original target field even when its weight vector is empty. -/
theorem originalChildRecords_nonempty (r : OriginalChildRequest) :
    ∀ x∈(compileL r.weights r.target).map (recBits r.W),x≠[] := by
  intro x hx
  obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
  have hn:=compileL_length r.weights r.target c hc
  have hl : (recBits r.W c).length=c.length*(r.W+1) := by
    unfold recBits
    rw [List.length_flatMap]
    simp only [SignedSortKey.binary_length,List.map_const',List.sum_replicate,smul_eq_mul]
  intro hh
  rw [hh] at hl
  simp only [List.length_nil] at hl
  nlinarith

/-- `prop:time`, paper/paper.tex: the source machine and literal record-copy pass both contribute to the outer framing budget. -/
def childFrameSteps (r : OriginalChildRequest) : ℕ :=
  2*(2*r.budget+2)+1+r.output.length*100+20

/-- `lem:print`, paper/paper.tex: the original-child compiler is followed by a literal record scan, rather than an assumed framed child tape. -/
noncomputable def childFrameProgram : WMX (childFrameTapes+1) 2 :=
  .seq (.machZ originalChildPrinter.program.machine childFrameMap childFrameRuler)
    (.wm (.seq (CounterAsm.frameLoop childFrameSource 1
      (fun b=>emitPair childFrameOut 0 b)) (emitC childFrameOut 0 false)))

/-- `prop:time`, paper/paper.tex: the run ruler contains only blank cells and the original child computation's full clock. -/
noncomputable def childFrameLens (r : OriginalChildRequest) (i : Fin (childFrameTapes+2)) : ℕ :=
  if i=childFrameRuler then 2*r.budget+2 else 0

/-- `lem:print` and `prop:time`, paper/paper.tex: the checked original decomposition is physically followed by its exact outer record frame. -/
theorem childFrameProgram_run (r : OriginalChildRequest) :
    Runs (2*r.output.length+2) childFrameProgram
      (idealStart (childFrameTapes+1) 2 r.word (childFrameLens r)) (childFrameSteps r)
      (fun τ=>τ.st childFrameOut=frame r.output) := by
  let σ:=idealStart (childFrameTapes+1) 2 r.word (childFrameLens r)
  have ht : 2≤childFrameTapes:=originalChildPrinter.program.twoTapes
  have hOut0 : childFrameOut.val≠0 := by change childFrameTapes≠0;omega
  have hRuler0 : childFrameRuler.val≠0 := by change childFrameTapes+1≠0;omega
  have hRulerNe : childFrameRuler≠0 := fun h=>hRuler0 (congrArg Fin.val h)
  have hOutRuler : childFrameOut≠childFrameRuler := by
    intro h
    have hh:=congrArg Fin.val h
    change childFrameTapes=childFrameTapes+1 at hh
    omega
  obtain ⟨rf,hr,hout⟩:=originalChildPrinter.realizes r
  have hin : (fun j=>σ.st (childFrameMap j))=originalChildPrinter.program.inputTapes r.word := by
    funext j
    simp only [σ,idealStart,childFrameMap,Fin.val_mk]
    split_ifs with hj
    · simp [RepairOrdinary.Program.inputTapes,hj]
    · have hne : (⟨j.val,by omega⟩:Fin (childFrameTapes+2))≠childFrameRuler := by
        intro h;have hh:=congrArg Fin.val h;have:=j.isLt
        simp only [childFrameRuler,Fin.val_mk] at hh;omega
      simp [childFrameLens,hne,RepairOrdinary.Program.inputTapes,hj]
  rw [←hin] at hr
  have hmap : Function.Injective childFrameMap := by
    intro i j h
    exact Fin.ext (congrArg (fun x:Fin (childFrameTapes+2)=>x.val) h)
  have hfar : ∀j,childFrameMap j≠childFrameRuler := by
    intro j h;have hh:=congrArg Fin.val h;have:=j.isLt
    simp only [childFrameMap,childFrameRuler,Fin.val_mk] at hh;omega
  obtain ⟨τ,e,dock⟩:=WXExec.machZ_run (cap:=2*r.output.length+2) hmap hfar σ hr
    (fun _=>rfl) (by simp [σ,idealStart,childFrameLens,hRulerNe]) rfl le_rfl
  have hs : τ.st childFrameSource=r.output := by
    change τ.st (childFrameMap originalChildPrinter.program.outputTape)=_
    rw [dock.st,hout]
  have ho : τ.st childFrameOut=[] := by
    have hh:=dock.other childFrameOut (by
      intro j h
      have hv:=congrArg (fun x:Fin (childFrameTapes+2)=>x.val) h
      have hlt:=j.isLt
      simp only [childFrameMap,childFrameOut,Fin.val_mk] at hv
      omega)
    rw [hh.1]
    change (if childFrameOut.val=0 then frame r.word else
      List.replicate (childFrameLens r childFrameOut) false)=[]
    rw [if_neg hOut0,childFrameLens,if_neg hOutRuler]
    rfl
  have hhh : ∀i,τ.sh i=0 := by
    intro i
    by_cases hx:∃j,childFrameMap j=i
    · obtain ⟨j,rfl⟩:=hx;exact dock.sh j
    · simpa only [σ,idealStart] using (dock.other i (by intro j h;exact hx ⟨j,h⟩)).2
  have hv : ∀q,τ.val q=0 := fun q=>by rw [dock.val];rfl
  have hso : childFrameSource≠childFrameOut := by
    intro h;have hh:=congrArg Fin.val h
    have:=originalChildPrinter.program.outputTape.isLt
    change originalChildPrinter.program.outputTape.val<childFrameTapes at this
    change originalChildPrinter.program.outputTape.val=childFrameTapes at hh
    omega
  have hcopy:=CounterAsm.frameLoop_spec (cap:=2*r.output.length+2)
    hso (by decide : (0:Fin 2)≠1)
    (NearCubicGates.Close.Recovery.HTParts.emits_pair (cap:=2*r.output.length+2)
      (dst:=childFrameOut) (OP:=0))
    (d:=2) (by intro b;simp) [] (by simp)
    ((compileL r.weights r.target).map (recBits r.W)) [] τ
    (originalChildRecords_nonempty r)
    (by simpa [OriginalChildRequest.output,compRecs,List.flatMap_map] using hs)
    (hhh _) (by rw [ho,hhh];rfl) (by
      rw [hv]
      simp [OriginalChildRequest.output,compRecs,List.flatMap_map]
      )
    (by
      rw [hv]
      simp [OriginalChildRequest.output,compRecs,List.flatMap_map]
      omega)
  let ρ:=adv childFrameSource childFrameOut 0 1 τ
    (r.output.flatMap fun b=>[true,b]) r.output.length
  have hp : WExec (2*r.output.length+2)
      (CounterAsm.frameLoop childFrameSource 1 (fun b=>emitPair childFrameOut 0 b)) τ ρ
      (r.output.length*57+1) := by
    simpa [ρ,OriginalChildRequest.output,compRecs,List.flatMap_map] using hcopy
  have hlen : (r.output.flatMap fun b=>[true,b]).length=2*r.output.length := by simp;omega
  have hrho : ρ.sh childFrameOut=(ρ.st childFrameOut).length := by
    rw [show ρ=adv childFrameSource childFrameOut 0 1 τ
      (r.output.flatMap fun b=>[true,b]) r.output.length from rfl,
      adv_sh_dst hso,adv_st_dst,ho,hhh]
    simp
  have hemit:=Codec.emitBit_spec (2*r.output.length+2) childFrameOut 0 false ρ hrho
    (by rw [show ρ=adv childFrameSource childFrameOut 0 1 τ
      (r.output.flatMap fun b=>[true,b]) r.output.length from rfl,adv_val_OP (by decide),hv,hlen];omega)
  refine (Runs.seqE e (Runs.of (WXExec.wm (hp.seq hemit)) ?_)).cost (by unfold childFrameSteps;omega)
  simp only [appendO,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
  rw [show ρ=adv childFrameSource childFrameOut 0 1 τ
    (r.output.flatMap fun b=>[true,b]) r.output.length from rfl,adv_st_dst,ho]
  simp [frame_eq_frameP,frameP]

end NearQuarticWires.StagePrint
