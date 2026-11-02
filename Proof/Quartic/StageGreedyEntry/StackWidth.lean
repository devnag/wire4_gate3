import Proof.Quartic.StageGreedyEntry.Modulus

/-!
# Retaining the actual stack width after the formatter call

Paper: `lem:print`, paper/paper.tex.

After the formatter, the retained prefix `natWord a ++ natWord b` stands in front of the literal
tuple request `t.word`, whose fifth field is `natWord t.stackWidth`. `stackP` copies the two prefix
fields, the bits of that fifth field and the whole request, and frames the result:
`frame (natWord a ++ natWord b ++ natWord t.stackWidth ++ t.word)` (`stackP_run`). No field is decoded.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint

/-- `lem:print`, paper/paper.tex: the eleven framed fields of the tuple request. -/
def twFields (t : StageTuple.TermCutRequest) : List (List Bool) :=
  [frame (callWord t.header.call),frame ((Header.baseHeaderValues t.header).flatMap natWord),t.contextWord,
    termsWord t.terms,natWord t.stackWidth,natWord t.degree,[],[],[],[],[]]

theorem tw_frames (t : StageTuple.TermCutRequest) : t.word=(twFields t).flatMap frame := by
  simp [twFields,StageTuple.TermCutRequest.word,Top.loadRec]

def sOP : Fin 5 := 0
def sS0 : Fin 5 := 1
def sSX : Fin 5 := 2
def sK : Fin 5 := 3
def sXO : Fin 5 := 4

/-- `lem:print`, paper/paper.tex: the physical program. -/
def stackP : WM 2 5 :=
  .seq (unframeP 0 2 sS0 sXO)
  (.seq (WM.rewind 2 sXO)
  (.seq (natCopy 2 sSX sK (fun b=>emitPair 1 sOP b))
  (.seq (natCopy 2 sSX sK (fun b=>emitPair 1 sOP b))
  (.seq (framesCopy 2 sSX (fun _=>.skip) 4)
  (.seq (markCopyP 2 1 sSX sOP)
  (.seq (WM.rewind 2 sSX)
  (.seq (natCopy 2 sSX sK (fun _=>.skip))
  (.seq (natCopy 2 sSX sK (fun _=>.skip))
  (.seq (framesCopy 2 sSX (fun b=>emitPair 1 sOP b) 11)
    (emitC 1 sOP false))))))))))

/-- `prop:time`, paper/paper.tex: a linear clock. -/
def stackCost (L : ℕ) : ℕ := 1000*(L+1)

theorem stackP_run (a b : ℕ) (t : StageTuple.TermCutRequest) :
    ∃τ : WState 2 5,WExec (10*((natWord a++(natWord b++t.word)).length+1)) stackP
      (idealStart 2 5 (natWord a++(natWord b++t.word)) (fun _=>0)) τ
      (stackCost (natWord a++(natWord b++t.word)).length) ∧
      τ.st 1=frame (natWord a++(natWord b++(natWord t.stackWidth++t.word))) := by
  set I:=natWord a++(natWord b++t.word) with hI
  set cap:=10*(I.length+1) with hcap
  obtain ⟨A,hA⟩ : ∃A,A=natWord a := ⟨_,rfl⟩
  obtain ⟨B,hB⟩ : ∃B,B=natWord b := ⟨_,rfl⟩
  obtain ⟨F,hF⟩ : ∃F,F=((twFields t).take 4).flatMap frame := ⟨_,rfl⟩
  obtain ⟨S,hS⟩ : ∃S,S=natWord t.stackWidth := ⟨_,rfl⟩
  obtain ⟨G,hG⟩ : ∃G,G=((twFields t).drop 5).flatMap frame := ⟨_,rfl⟩
  have hTW : t.word=F++frame S++G := by
    rw [tw_frames,hF,hS,hG]
    simp [twFields]
  have hIw : I=A++B++F++frame S++G := by rw [hI,hTW,hA,hB];simp [List.append_assoc]
  have hlen : I.length=A.length+B.length+F.length+(2*S.length+1)+G.length := by
    rw [hIw];simp only [List.length_append,frame_length]
  set σ0:=idealStart 2 5 I (fun _=>0) with hσ0
  have s0 : σ0.st 0=frame I := by simp [hσ0,idealStart]
  have s1 : σ0.st 1=[] := by simp [hσ0,idealStart]
  have s2 : σ0.st 2=[] := by simp [hσ0,idealStart]
  have h0 (i : Fin 3) : σ0.sh i=0 := by simp [hσ0,idealStart]
  have v0 (x : Fin 5) : σ0.val x=0 := by simp [hσ0,idealStart]
  have e1:=unframe_spec cap (src:=0) (dst:=2) (OP:=sXO) (SC:=sS0) (by decide) (by decide) I [] [] σ0
    (by rw [s0];simp) (by rw [h0];rfl) (by rw [s2,h0];rfl) (by rw [v0];omega) (by rw [v0];omega)
  set σ1:=adv 0 2 sXO sS0 σ0 I (2*I.length+1) with hσ1
  have e2:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (2 : Fin 3) sXO I.length σ1
    (by rw [hσ1,adv_val_OP (by decide),v0];simp) (by rw [hσ1,adv_val_OP (by decide),v0];omega)
  set σ2:=(σ1.setv sXO 0).seth 2 (σ1.sh 2-I.length) with hσ2
  have t2 : σ2.st 2=I := by
    simp only [hσ2,WState.seth_st,WState.setv_st,hσ1,adv_st_dst,s2,List.nil_append]
  have t1 : σ2.st 1=[] := by
    simp only [hσ2,WState.seth_st,WState.setv_st,hσ1]
    rw [adv_st_other _ _ _ 1 (by decide),s1]
  have g2 : σ2.sh 2=0 := by
    simp only [hσ2,WState.seth_sh,Function.update_self,hσ1]
    rw [adv_sh_dst (by decide),h0];simp
  have g1 : σ2.sh 1=0 := by
    simp only [hσ2,WState.seth_sh,WState.setv_sh,hσ1]
    rw [Function.update_of_ne (by decide),adv_sh_other _ _ _ 1 (by decide) (by decide),h0]
  have u (x : Fin 5) (h1 : x≠sXO) (h2 : x≠sS0) : σ2.val x=0 := by
    simp only [hσ2,WState.seth_val,WState.setv_val,hσ1]
    rw [Function.update_of_ne h1,adv_val_other _ _ _ x h1 h2,v0]
  have nE : Emits cap (1 : Fin 3) sOP (fun _=>[]) (fun _=>WM.skip) 0 := emits_none cap
  have nL : EmitLen (fun _ : Bool=>([] : List Bool)) 0 := fun _=>by simp
  have pE : Emits cap (1 : Fin 3) sOP (fun b=>[true,b]) (fun b=>emitPair 1 sOP b) 15 := emits_pair cap
  have pL : EmitLen (fun b : Bool=>[true,b]) 2 := fun _=>by simp
  have rE : Emits cap (1 : Fin 3) sOP (fun b=>[b]) (fun b=>emitC 1 sOP b) 7 := emits_raw cap
  -- the two retained naturals
  have e3:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (K:=sK) (by decide) (by decide)
    (by decide) (by decide) pE pL a [] (B++F++frame S++G) σ2
    (by rw [t2,hIw,hA];simp [List.append_assoc]) (by rw [g2];rfl) (by rw [g1,t1];rfl)
    (u sK (by decide) (by decide)) (by rw [u sOP (by decide) (by decide),←hA];omega)
    (by rw [u sSX (by decide) (by decide),←hA];omega) (by rw [←hA];omega)
  rw [flatMap_pair,←hA] at e3
  set σ3:=adv 2 1 sOP sSX σ2 (Streaming.marks A) A.length with hσ3
  have e4:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (K:=sK) (by decide) (by decide)
    (by decide) (by decide) pE pL b A (F++frame S++G) σ3
    (by rw [hσ3,adv_st_src (by decide),t2,hIw,hB];simp [List.append_assoc])
    (by rw [hσ3,adv_sh_src,g2];simp)
    (by rw [hσ3,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [hσ3,adv_val_other _ _ _ sK (by decide) (by decide),u sK (by decide) (by decide)])
    (by rw [hσ3,adv_val_OP (by decide),u sOP (by decide) (by decide),←hB,Streaming.marks_length];omega)
    (by rw [hσ3,adv_val_SC,u sSX (by decide) (by decide),←hB];omega) (by rw [←hB];omega)
  rw [flatMap_pair,←hB] at e4
  set σ4:=adv 2 1 sOP sSX σ3 (Streaming.marks B) B.length with hσ4
  have σ4e : σ4=adv 2 1 sOP sSX σ2 (Streaming.marks A++Streaming.marks B) (A.length+B.length) := by
    rw [hσ4,hσ3,adv_adv (by decide) (by decide)]
  -- the first four request fields, then the marked stack width
  have e5:=framesCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (by decide) (by decide)
    nE nL ((twFields t).take 4) (A++B) (frame S++G) σ4
    (by rw [σ4e,adv_st_src (by decide),t2,hIw,hF];simp [List.append_assoc])
    (by rw [σ4e,adv_sh_src,g2];simp)
    (by rw [σ4e,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [σ4e,adv_val_OP (by decide),u sOP (by decide) (by decide)];simp;omega)
    (by rw [σ4e,adv_val_SC,u sSX (by decide) (by decide),←hF];omega)
  rw [←hF,flatMap_nil',show ((twFields t).take 4).length=4 from rfl] at e5
  set σ5:=adv 2 1 sOP sSX σ4 [] F.length with hσ5
  have σ5e : σ5=adv 2 1 sOP sSX σ2 (Streaming.marks A++Streaming.marks B) (A.length+B.length+F.length) := by
    rw [hσ5,σ4e,adv_adv (by decide) (by decide)];simp
  have e6:=markCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (by decide) (by decide)
    S (A++B++F) G σ5
    (by rw [σ5e,adv_st_src (by decide),t2,hIw])
    (by rw [σ5e,adv_sh_src,g2];simp;omega)
    (by rw [σ5e,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [σ5e,adv_val_OP (by decide),u sOP (by decide) (by decide)];simp;omega)
    (by rw [σ5e,adv_val_SC,u sSX (by decide) (by decide)];omega)
  set σ6:=adv 2 1 sOP sSX σ5 (Streaming.marks S) (2*S.length+1) with hσ6
  have σ6e : σ6=adv 2 1 sOP sSX σ2 (Streaming.marks A++Streaming.marks B++Streaming.marks S)
      (A.length+B.length+F.length+(2*S.length+1)) := by
    rw [hσ6,σ5e,adv_adv (by decide) (by decide)]
  -- rewind the decoded entry and copy the whole request, marked
  have e7:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (2 : Fin 3) sSX
    (A.length+B.length+F.length+(2*S.length+1)) σ6
    (by rw [σ6e,adv_val_SC,u sSX (by decide) (by decide)];simp) (by rw [σ6e,adv_val_SC,u sSX (by decide) (by decide)];omega)
  set σ7:=(σ6.setv sSX 0).seth 2 (σ6.sh 2-(A.length+B.length+F.length+(2*S.length+1))) with hσ7
  have t7_2 : σ7.st 2=I := by simp only [hσ7,WState.seth_st,WState.setv_st,σ6e];rw [adv_st_src (by decide),t2]
  have g7_2 : σ7.sh 2=0 := by
    simp only [hσ7,WState.seth_sh,Function.update_self,σ6e];rw [adv_sh_src,g2];simp
  have t7_1 : σ7.st 1=Streaming.marks A++Streaming.marks B++Streaming.marks S := by
    simp only [hσ7,WState.seth_st,WState.setv_st,σ6e];rw [adv_st_dst,t1];simp
  have g7_1 : σ7.sh 1=(σ7.st 1).length := by
    rw [t7_1];simp only [hσ7,WState.seth_sh,WState.setv_sh]
    rw [Function.update_of_ne (by decide),σ6e,adv_sh_dst (by decide),g1];simp
  have u7 (x : Fin 5) (h1 : x≠sXO) (h2 : x≠sS0) (h3 : x≠sOP) : σ7.val x=0 := by
    by_cases hx : x=sSX
    · rw [hx];simp [hσ7]
    · simp only [hσ7,WState.seth_val,WState.setv_val]
      rw [Function.update_of_ne hx,σ6e,adv_val_other _ _ _ x h3 hx,u x h1 h2]
  have u7OP : σ7.val sOP=2*A.length+2*B.length+2*S.length := by
    simp only [hσ7,WState.seth_val,WState.setv_val]
    rw [Function.update_of_ne (by decide),σ6e,adv_val_OP (by decide),u sOP (by decide) (by decide)]
    simp [Streaming.marks_length];ring
  have e8:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (K:=sK) (by decide) (by decide)
    (by decide) (by decide) nE nL a [] (B++F++frame S++G) σ7
    (by rw [t7_2,hIw,hA];simp [List.append_assoc]) (by rw [g7_2];rfl) g7_1
    (u7 sK (by decide) (by decide) (by decide)) (by rw [u7OP];simp;omega)
    (by rw [u7 sSX (by decide) (by decide) (by decide),←hA];omega) (by rw [←hA];omega)
  rw [flatMap_nil',←hA] at e8
  set σ8:=adv 2 1 sOP sSX σ7 [] A.length with hσ8
  have e9:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (K:=sK) (by decide) (by decide)
    (by decide) (by decide) nE nL b A (F++frame S++G) σ8
    (by rw [hσ8,adv_st_src (by decide),t7_2,hIw,hB];simp [List.append_assoc])
    (by rw [hσ8,adv_sh_src,g7_2];simp)
    (by rw [hσ8,adv_sh_dst (by decide),adv_st_dst,g7_1];simp)
    (by rw [hσ8,adv_val_other _ _ _ sK (by decide) (by decide),u7 sK (by decide) (by decide) (by decide)])
    (by rw [hσ8,adv_val_OP (by decide),u7OP];simp;omega)
    (by rw [hσ8,adv_val_SC,u7 sSX (by decide) (by decide) (by decide),←hB];omega) (by rw [←hB];omega)
  rw [flatMap_nil',←hB] at e9
  set σ9:=adv 2 1 sOP sSX σ8 [] B.length with hσ9
  have σ9e : σ9=adv 2 1 sOP sSX σ7 [] (A.length+B.length) := by
    rw [hσ9,hσ8,adv_adv (by decide) (by decide)];rfl
  have e10:=framesCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=sOP) (SC:=sSX) (by decide) (by decide)
    pE pL (twFields t) (A++B) [] σ9
    (by rw [σ9e,adv_st_src (by decide),t7_2,hI,←tw_frames,hA,hB];simp [List.append_assoc])
    (by rw [σ9e,adv_sh_src,g7_2];simp)
    (by rw [σ9e,adv_sh_dst (by decide),adv_st_dst,g7_1];simp)
    (by rw [σ9e,adv_val_OP (by decide),u7OP,←tw_frames,hTW];simp only [List.length_append,frame_length,
      List.length_nil];omega)
    (by rw [σ9e,adv_val_SC,u7 sSX (by decide) (by decide) (by decide),←tw_frames,hTW];
        simp only [List.length_append,frame_length];omega)
  rw [←tw_frames,flatMap_pair,show (twFields t).length=11 from rfl] at e10
  set σ10:=adv 2 1 sOP sSX σ9 (Streaming.marks t.word) t.word.length with hσ10
  have e11:=rE false σ10
    (by rw [hσ10,adv_sh_dst (by decide),adv_st_dst,σ9e,adv_sh_dst (by decide),adv_st_dst,g7_1];simp)
    (by rw [hσ10,adv_val_OP (by decide),σ9e,adv_val_OP (by decide),u7OP,hTW,Streaming.marks_length];
        simp only [List.length_append,frame_length,List.length_nil,List.length_cons];omega)
  refine ⟨_,WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11)))))))))) ?_,?_⟩
  · simp only [stackCost,frame_length]
    rw [hTW] at *
    simp only [List.length_append,frame_length] at *
    omega
  · rw [appendO_st,Function.update_self,hσ10,adv_st_dst,σ9e,adv_st_dst,t7_1,hA,hB,hS]
    rw [NearCubicGates.Close.Codec.frame_eq_marks]
    simp [Streaming.marks_append,List.append_assoc]

end NearQuarticWires.StageGreedyEntry
