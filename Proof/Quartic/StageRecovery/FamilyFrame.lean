import Proof.Quartic.StageRecovery.FamilyMachine
import Proof.Gates.CounterAsm.Copy
import Proof.Gates.TabMachine.Occ

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the finite support-family machine's complete fixed tape bank. -/
noncomputable abbrev familyFrameTapes : ℕ := familyWordFunction.program.tapeCount

/-- `lem:print`, paper/paper.tex: the family machine uses the initial bank without sharing its work tapes with the record framer. -/
def familyFrameMap (j : Fin familyFrameTapes) : Fin (familyFrameTapes+2) := ⟨j.val,by omega⟩

/-- `lem:print`, paper/paper.tex: the exact family stream is the subsequent physical framer's source. -/
noncomputable def familyFrameSource : Fin (familyFrameTapes+2) :=
  familyFrameMap familyWordFunction.program.outputTape

/-- `lem:print`, paper/paper.tex: a fresh tape stores the outer frame around all generated supports. -/
noncomputable def familyFrameOut : Fin (familyFrameTapes+2) := ⟨familyFrameTapes,by omega⟩

/-- `lem:print`, paper/paper.tex: the finite run ruler is separate from both the family bank and its framed output. -/
noncomputable def familyFrameRuler : Fin (familyFrameTapes+2) := ⟨familyFrameTapes+1,by omega⟩

/-- `lem:print`, paper/paper.tex: the fixed positive width makes every generated support record nonempty. -/
theorem familyRecords_nonempty (r : FamilyRequest) :
    ∀ x ∈ (NearCubicGates.Close.Expand.famRecs r.arity r.degree).map (binary r.width), x ≠ [] := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  intro he
  have hh := congrArg List.length he
  simp only [SignedSortKey.binary_length, List.length_nil] at hh
  unfold FamilyRequest.width at hh
  omega

/-- `lem:print`, paper/paper.tex: the native
family packet has its explicit final record-stream delimiter. -/
def FamilyRequest.recordBody (r : FamilyRequest) : List Bool :=
  (NearCubicGates.Close.Expand.famRecs r.arity r.degree).flatMap (fun v => frame (binary r.width v))

/-- `lem:print`, paper/paper.tex: the record body
and its last false bit are precisely the complete native packet. -/
theorem FamilyRequest.output_eq_body (r : FamilyRequest) : r.output = r.recordBody ++ [false] := by
  simp [FamilyRequest.output, FamilyRequest.recordBody, recStream, List.flatMap_map]

/-- `prop:time`, paper/paper.tex: the source machine and literal record-copy pass both contribute to the outer framing budget. -/
def familyFrameSteps (r : FamilyRequest) : ℕ :=
  2*r.budget+2+1+r.output.length*100+20

/-- `lem:print`, paper/paper.tex: the family compiler is followed by a literal record scan, with its literal final packet delimiter. -/
noncomputable def familyFrameProgram : WMX (familyFrameTapes+1) 2 :=
  .seq (.machZ familyWordFunction.program.machine familyFrameMap familyFrameRuler)
    (.wm (.seq (CounterAsm.frameLoop familyFrameSource 1
      (fun b=>emitPair familyFrameOut 0 b)) (.seq (emitPair familyFrameOut 0 false) (emitC familyFrameOut 0 false))))

/-- `prop:time`, paper/paper.tex: the run ruler contains only blank cells and the generated family computation's full clock. -/
noncomputable def familyFrameLens (r : FamilyRequest) (i : Fin (familyFrameTapes+2)) : ℕ :=
  if i=familyFrameRuler then r.budget else 0

/-- `lem:print` and `prop:time`, paper/paper.tex: the checked support generation is physically followed by its exact outer record frame. -/
theorem familyFrameProgram_run (r : FamilyRequest) :
    Runs (2*r.output.length+2) familyFrameProgram
      (idealStart (familyFrameTapes+1) 2 r.word (familyFrameLens r)) (familyFrameSteps r)
      (fun τ=>τ.st familyFrameOut=frame r.output) := by
  let σ:=idealStart (familyFrameTapes+1) 2 r.word (familyFrameLens r)
  have ht : 2≤familyFrameTapes:=familyWordFunction.program.twoTapes
  have hOut0 : familyFrameOut.val≠0 := by change familyFrameTapes≠0;omega
  have hRuler0 : familyFrameRuler.val≠0 := by change familyFrameTapes+1≠0;omega
  have hRulerNe : familyFrameRuler≠0 := fun h=>hRuler0 (congrArg Fin.val h)
  have hOutRuler : familyFrameOut≠familyFrameRuler := by
    intro h
    have hh:=congrArg Fin.val h
    change familyFrameTapes=familyFrameTapes+1 at hh
    omega
  obtain ⟨rf,hr,hout⟩:=familyWordFunction.realizes r
  have hin : (fun j=>σ.st (familyFrameMap j))=familyWordFunction.program.inputTapes r.word := by
    funext j
    simp only [σ,idealStart,familyFrameMap,Fin.val_mk]
    split_ifs with hj
    · simp [RepairOrdinary.Program.inputTapes,hj]
    · have hne : (⟨j.val,by omega⟩:Fin (familyFrameTapes+2))≠familyFrameRuler := by
        intro h;have hh:=congrArg Fin.val h;have:=j.isLt
        simp only [familyFrameRuler,Fin.val_mk] at hh;omega
      simp [familyFrameLens,hne,RepairOrdinary.Program.inputTapes,hj]
  rw [←hin] at hr
  have hmap : Function.Injective familyFrameMap := by
    intro i j h
    exact Fin.ext (congrArg (fun x:Fin (familyFrameTapes+2)=>x.val) h)
  have hfar : ∀j,familyFrameMap j≠familyFrameRuler := by
    intro j h;have hh:=congrArg Fin.val h;have:=j.isLt
    simp only [familyFrameMap,familyFrameRuler,Fin.val_mk] at hh;omega
  obtain ⟨τ,e,dock⟩:=WXExec.machZ_run (cap:=2*r.output.length+2) hmap hfar σ hr
    (fun _=>rfl) (by simp [σ,idealStart,familyFrameLens,hRulerNe]) rfl le_rfl
  have hs : τ.st familyFrameSource=r.output := by
    change τ.st (familyFrameMap familyWordFunction.program.outputTape)=_
    rw [dock.st,hout]
  have ho : τ.st familyFrameOut=[] := by
    have hh:=dock.other familyFrameOut (by
      intro j h
      have hv:=congrArg (fun x:Fin (familyFrameTapes+2)=>x.val) h
      have hlt:=j.isLt
      simp only [familyFrameMap,familyFrameOut,Fin.val_mk] at hv
      omega)
    rw [hh.1]
    change (if familyFrameOut.val=0 then frame r.word else
      List.replicate (familyFrameLens r familyFrameOut) false)=[]
    rw [if_neg hOut0,familyFrameLens,if_neg hOutRuler]
    rfl
  have hhh : ∀i,τ.sh i=0 := by
    intro i
    by_cases hx:∃j,familyFrameMap j=i
    · obtain ⟨j,rfl⟩:=hx;exact dock.sh j
    · simpa only [σ,idealStart] using (dock.other i (by intro j h;exact hx ⟨j,h⟩)).2
  have hv : ∀q,τ.val q=0 := fun q=>by rw [dock.val];rfl
  have hso : familyFrameSource≠familyFrameOut := by
    intro h;have hh:=congrArg Fin.val h
    have:=familyWordFunction.program.outputTape.isLt
    change familyWordFunction.program.outputTape.val<familyFrameTapes at this
    change familyWordFunction.program.outputTape.val=familyFrameTapes at hh
    omega
  have hbodylen : r.output.length = r.recordBody.length + 1 := by rw [r.output_eq_body]; simp
  have hcopy:=CounterAsm.frameLoop_spec (cap:=2*r.output.length+2)
    hso (by decide : (0:Fin 2)≠1)
    (NearCubicGates.Close.Recovery.HTParts.emits_pair (cap:=2*r.output.length+2)
      (dst:=familyFrameOut) (OP:=0))
    (d:=2) (by intro b;simp) [false] (by simp)
    ((NearCubicGates.Close.Expand.famRecs r.arity r.degree).map (binary r.width)) [] τ
    (familyRecords_nonempty r)
    (by simpa [FamilyRequest.output,FamilyRequest.recordBody,recStream,List.flatMap_map] using hs)
    (hhh _) (by rw [ho,hhh];rfl) (by
      rw [hv]
      simp [FamilyRequest.output,FamilyRequest.recordBody,recStream,List.flatMap_map]
      omega)
    (by
      rw [hv]
      simp [FamilyRequest.output,FamilyRequest.recordBody,recStream,List.flatMap_map]
      omega)
  let ρ:=adv familyFrameSource familyFrameOut 0 1 τ
    (r.recordBody.flatMap fun b=>[true,b]) r.recordBody.length
  have hp : WExec (2*r.output.length+2)
      (CounterAsm.frameLoop familyFrameSource 1 (fun b=>emitPair familyFrameOut 0 b)) τ ρ
      (r.recordBody.length*57+1) := by
    simpa [ρ,FamilyRequest.output,FamilyRequest.recordBody,recStream,List.flatMap_map] using hcopy
  have hlen : (r.recordBody.flatMap fun b=>[true,b]).length=2*r.recordBody.length := by simp;omega
  have hrho : ρ.sh familyFrameOut=(ρ.st familyFrameOut).length := by
    rw [show ρ=adv familyFrameSource familyFrameOut 0 1 τ
      (r.recordBody.flatMap fun b=>[true,b]) r.recordBody.length from rfl,
      adv_sh_dst hso,adv_st_dst,ho,hhh]
    simp
  have hvalρ : ρ.val (0 : Fin 2) = 2 * r.recordBody.length := by
    change (adv familyFrameSource familyFrameOut 0 1 τ
      (r.recordBody.flatMap fun b => [true,b]) r.recordBody.length).val 0 = _
    rw [adv_val_OP (by decide), hv, hlen]
    omega
  have hp2 := emitPair_spec (2*r.output.length+2) familyFrameOut (0 : Fin 2) false ρ hrho
    (by rw [hvalρ, hbodylen]; omega)
  let ρ2 := appendO ρ familyFrameOut (0 : Fin 2) [true,false]
  have hρ2head : ρ2.sh familyFrameOut = (ρ2.st familyFrameOut).length := by
    simp [ρ2, appendO, hrho, List.length_append]
  have hρ2val : ρ2.val (0 : Fin 2) + 1 ≤ 2*r.output.length+2 := by
    simp [ρ2, appendO, hvalρ, hbodylen]
  have hemit := Codec.emitBit_spec (2*r.output.length+2) familyFrameOut 0 false ρ2 hρ2head hρ2val
  refine (Runs.seqE e (Runs.of (WXExec.wm (hp.seq (hp2.seq hemit))) ?_)).cost
    (by unfold familyFrameSteps; rw [hbodylen]; omega)
  simp only [appendO,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
  rw [show ρ2 = appendO ρ familyFrameOut (0 : Fin 2) [true,false] from rfl]
  simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
  rw [show ρ=adv familyFrameSource familyFrameOut 0 1 τ
    (r.recordBody.flatMap fun b=>[true,b]) r.recordBody.length from rfl,adv_st_dst,ho,
    r.output_eq_body]
  simp [frame_eq_frameP,frameP,List.flatMap_append,List.append_assoc]

end NearQuarticWires.StageRecovery
