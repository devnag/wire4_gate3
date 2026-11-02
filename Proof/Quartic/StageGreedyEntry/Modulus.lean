import Proof.Quartic.StageGreedyEntry.Copy
import Proof.Quartic.StageGreedyEntry.Half
import Proof.Quartic.StageGreedyEntry.Format
import Proof.Gates.Expand.PolyTabPack
import Proof.Wire_3_5.PrimAsmCopyNat

/-!
# Retaining the dense width and the binary modulus before the formatter call

Paper: `lem:print` and `lem:residue`, paper/paper.tex.

The entry word is `natWord n ++ context ++ natWord walk ++ natWord D ++ natWord modulus ++ frame terms`.
`prefixP` decodes its frame onto a work stream, reads the small original arity `n` and writes the dense
width `(n+1)/2` (`width_eq`), passes over the eleven context frames, the walk ordinal and the degree
without decoding them, copies the bits of the modulus field, and then copies the whole entry. Its output is
`frame (natWord ((n+1)/2) ++ natWord modulus ++ word)` (`prefixWordFunction`). The modulus and the walk
ordinal are never decoded.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint

/-- `lem:print`, paper/paper.tex: the eleven framed fields of the retained context. -/
def ctxFields {modular : Bool} (r : EntryFormat.Request modular) : List (List Bool) :=
  [frame (callWord r.header.call),frame ((Header.baseHeaderValues r.header).flatMap natWord),r.countsWord,
    [r.header.call.n,r.header.parameters.r,r.header.parameters.b,r.header.parameters.s].flatMap natWord,
    [],[],[],[],[],[],[]]

theorem contextWord_frames {modular : Bool} (r : EntryFormat.Request modular) :
    r.contextWord=(ctxFields r).flatMap frame := by
  simp [ctxFields,EntryFormat.Request.contextWord,Top.loadRec]

theorem word_fields {modular : Bool} (r : EntryFormat.Request modular) :
    r.word=natWord r.header.call.n++(ctxFields r).flatMap frame++natWord r.walkCode.val++natWord r.degree++
      natWord r.scale++frame (termsWord r.terms) := by
  rw [←contextWord_frames]
  rfl

theorem frame_append_marks (a b : List Bool) : frame (a++b)=marks a++frame b := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks,NearCubicGates.Close.Codec.frame_eq_marks,
    NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]

theorem flatMap_pair (w : List Bool) : (w.flatMap fun b=>[true,b])=marks w := rfl

theorem flatMap_single : ∀ w : List Bool,(w.flatMap fun b=>[b])=w
  | []=>rfl
  | b::w=>by
    have h:=flatMap_single w
    simp only [List.flatMap_cons] at h ⊢
    rw [h];rfl

theorem flatMap_nil' (w : List Bool) : (w.flatMap fun _=>([] : List Bool))=[] := by simp

/-! ## Layout: stream `0` input, `1` output, `2` decoded entry. -/

def rOP : Fin 17 := 0
def rS0 : Fin 17 := 1
def rSX : Fin 17 := 2
def rK : Fin 17 := 3
def rXO : Fin 17 := 4
def pf : Fin 17 := 5
def pc : Fin 17 := 6
def pp : Fin 17 := 7
def pt : Fin 17 := 8
def rN : Fin 17 := 9
def rH : Fin 17 := 10

/-- The registers of the natural writer: value `rH`, scratch `11–16`, output counter `rOP`. -/
def wR : Fin 8 ↪ Fin 17 :=
  ⟨![10,11,12,13,14,15,16,0],by decide⟩

/-- `lem:print`, paper/paper.tex: the physical program. -/
def prefixP : WM 2 17 :=
  .seq (unframeP 0 2 rS0 rXO)
  (.seq (WM.rewind 2 rXO)
  (.seq (NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.readNatM false 2 pf pc rN pp pt)
  (.seq (.inc rN)
  (.seq (halfP rN rH)
  (.seq (writeNatM 1 wR)
  (.seq (framesCopy 2 rSX (fun _=>.skip) 11)
  (.seq (natCopy 2 rSX rK (fun _=>.skip))
  (.seq (natCopy 2 rSX rK (fun _=>.skip))
  (.seq (natCopy 2 rSX rK (fun b=>emitPair 1 rOP b))
  (.seq (WM.rewind 0 rS0)
    (frameCopy 0 rS0 (fun b=>emitC 1 rOP b))))))))))))

/-- `prop:time`, paper/paper.tex: a linear clock. -/
def prefixCost (L n : ℕ) : ℕ := 1000*(L+1)+10^4*(n+1)^2

theorem quad1 (n : ℕ) : (n+3)*(80*n+120)≤400*(n+1)^2 := by nlinarith

theorem quad2 (n : ℕ) : (n+12)*(100*n+300)≤3600*(n+1)^2 := by nlinarith

theorem prefixP_run {modular : Bool} (r : EntryFormat.Request modular) :
    ∃τ : WState 2 17,WExec (10*(r.word.length+1)+8*(r.header.call.n+1)) prefixP
      (idealStart 2 17 r.word (fun _=>0)) τ (prefixCost r.word.length r.header.call.n) ∧
      τ.st 1=frame (natWord ((r.header.call.n+1)/2)++natWord r.scale++r.word) := by
  set I:=r.word with hI
  set cap:=10*(I.length+1)+8*(r.header.call.n+1) with hcap
  obtain ⟨C,hC⟩ : ∃C,C=(ctxFields r).flatMap frame := ⟨_,rfl⟩
  have hIw : I=natWord r.header.call.n++C++natWord r.walkCode.val++natWord r.degree++
      natWord r.scale++frame (termsWord r.terms) := by rw [hC];exact word_fields r
  obtain ⟨n,hn⟩ : ∃n,n=natWord r.header.call.n := ⟨_,rfl⟩
  obtain ⟨wk,hwk⟩ : ∃wk,wk=natWord r.walkCode.val := ⟨_,rfl⟩
  obtain ⟨dg,hdg⟩ : ∃dg,dg=natWord r.degree := ⟨_,rfl⟩
  obtain ⟨q,hq⟩ : ∃q,q=natWord r.scale := ⟨_,rfl⟩
  obtain ⟨T,hT⟩ : ∃T,T=frame (termsWord r.terms) := ⟨_,rfl⟩
  rw [←hn,←hwk,←hdg,←hq,←hT] at hIw
  have hlen : I.length=n.length+C.length+wk.length+dg.length+q.length+T.length := by
    rw [hIw];simp only [List.length_append]
  set σ0:=idealStart 2 17 I (fun _=>0) with hσ0
  have s0 : σ0.st 0=frame I := by simp [hσ0,idealStart]
  have s1 : σ0.st 1=[] := by simp [hσ0,idealStart]
  have s2 : σ0.st 2=[] := by simp [hσ0,idealStart]
  have h0 (i : Fin 3) : σ0.sh i=0 := by simp [hσ0,idealStart]
  have v0 (x : Fin 17) : σ0.val x=0 := by simp [hσ0,idealStart]
  -- decode the entry onto stream 2
  have e1:=unframe_spec cap (src:=0) (dst:=2) (OP:=rXO) (SC:=rS0) (by decide) (by decide) I [] [] σ0
    (by rw [s0];simp) (by rw [h0];rfl) (by rw [s2,h0];rfl) (by rw [v0];omega) (by rw [v0];omega)
  set σ1:=adv 0 2 rXO rS0 σ0 I (2*I.length+1) with hσ1
  have e2:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (2 : Fin 3) rXO I.length σ1
    (by rw [hσ1,adv_val_OP (by decide),v0];simp) (by rw [hσ1,adv_val_OP (by decide),v0];omega)
  set σ2:=(σ1.setv rXO 0).seth 2 (σ1.sh 2-I.length) with hσ2
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
  have g0 : σ2.sh 0=2*I.length+1 := by
    simp only [hσ2,WState.seth_sh,WState.setv_sh,hσ1]
    rw [Function.update_of_ne (by decide),adv_sh_src,h0];simp
  have t0 : σ2.st 0=frame I := by
    simp only [hσ2,WState.seth_st,WState.setv_st,hσ1]
    rw [adv_st_src (by decide),s0]
  have u (x : Fin 17) (h1 : x≠rXO) (h2 : x≠rS0) : σ2.val x=0 := by
    simp only [hσ2,WState.seth_val,WState.setv_val,hσ1]
    rw [Function.update_of_ne h1,adv_val_other _ _ _ x h1 h2,v0]
  have uS0 : σ2.val rS0=2*I.length+1 := by
    simp only [hσ2,WState.seth_val,WState.setv_val,hσ1]
    rw [Function.update_of_ne (by decide),adv_val_SC,v0];simp
  -- read the arity and write the dense width
  have hpow:=NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.two_pow_natBitLength_le r.header.call.n
  have e3:=NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.readNatM_spec cap false (2 : Fin 3) pf pc rN pp pt
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) r.header.call.n [] (C++wk++dg++q++T) σ2
    (by rw [t2,hIw,hn];simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,List.append_assoc])
    (by rw [g2];rfl) (u pf (by decide) (by decide)) (u pc (by decide) (by decide))
    (u pp (by decide) (by decide)) (u pt (by decide) (by decide))
    (by rw [u rN (by decide) (by decide),pow_succ];omega)
  set σ3:=(σ2.seth 2 ([].length+NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false*
    (natWord r.header.call.n).length)).setv rN (σ2.val rN+r.header.call.n) with hσ3
  have v3N : σ3.val rN=r.header.call.n := by simp [hσ3,u rN (by decide) (by decide)]
  have e4:=WExec.inc (cap:=cap) rN σ3 (by rw [v3N];omega)
  set σ4:=σ3.setv rN (σ3.val rN+1) with hσ4
  have e5:=halfP_exec cap rN rH (by decide) (r.header.call.n+1) 0 σ4 (by simp [hσ4,v3N])
    (by simp [hσ4,hσ3,Function.update_of_ne (show rH≠rN by decide),u rH (by decide) (by decide)])
    (by omega) (by omega)
  set σ5:=(σ4.setv rN 0).setv rH (0+(r.header.call.n+1)/2) with hσ5
  have v5 (x : Fin 17) (h1 : x≠rN) (h2 : x≠rH) : σ5.val x=σ2.val x := by
    simp [hσ5,hσ4,hσ3,Function.update_of_ne h1,Function.update_of_ne h2]
  have e6:=writeNatM_spec cap (1 : Fin 3) wR σ5
    (by rw [show wR 1=11 from rfl,v5 _ (by decide) (by decide),u _ (by decide) (by decide)])
    (by rw [show wR 2=12 from rfl,v5 _ (by decide) (by decide),u _ (by decide) (by decide)])
    (by rw [show wR 3=13 from rfl,v5 _ (by decide) (by decide),u _ (by decide) (by decide)])
    (by rw [show wR 4=14 from rfl,v5 _ (by decide) (by decide),u _ (by decide) (by decide)])
    (by rw [show wR 5=15 from rfl,v5 _ (by decide) (by decide),u _ (by decide) (by decide)])
    (by rw [show wR 6=16 from rfl,v5 _ (by decide) (by decide),u _ (by decide) (by decide)])
    (by simp [hσ5,hσ4,hσ3,g1,t1])
    (by
      rw [show wR 0=rH from rfl,show wR 7=rOP from rfl,v5 rOP (by decide) (by decide),
        u rOP (by decide) (by decide)]
      have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (0+(r.header.call.n+1)/2)
      simp [hσ5] at hb ⊢
      omega)
  set W0:=(σ5.val (wR 0)) with hW0
  have hW0e : W0=(r.header.call.n+1)/2 := by simp [hW0,hσ5,show wR 0=rH from rfl]
  set σ6:=appendO σ5 1 (wR 7) (Streaming.marks (natWord W0)) with hσ6
  have t6_2 : σ6.st 2=I := by
    simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,t2]
  have g6_2 : σ6.sh 2=n.length := by
    simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,hn,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]
  have t6_1 : σ6.st 1=Streaming.marks (natWord W0) := by
    simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,t1]
  have g6_1 : σ6.sh 1=(σ6.st 1).length := by
    rw [t6_1];simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,g1,t1]
  have t6_0 : σ6.st 0=frame I := by simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,t0]
  have g6_0 : σ6.sh 0=2*I.length+1 := by simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,g0]
  have u6 (x : Fin 17) (h1 : x≠rXO) (h2 : x≠rS0) (h3 : x≠rN) (h4 : x≠rH) (h5 : x≠rOP) : σ6.val x=0 := by
    have := u x h1 h2
    simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,h3,h4,show wR 7=rOP from rfl,h5,this]
  have u6S0 : σ6.val rS0=2*I.length+1 := by
    simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,show wR 7=rOP from rfl,uS0,
      show rS0≠rOP by decide,show rS0≠rN by decide,show rS0≠rH by decide]
  have u6OP : σ6.val rOP=(Streaming.marks (natWord W0)).length := by
    simp [hσ6,hσ5,hσ4,hσ3,Function.update_apply,show wR 7=rOP from rfl,u rOP (by decide) (by decide),
      show rOP≠rN by decide,show rOP≠rH by decide]
  -- the parse on stream 2: the context, the walk ordinal, the degree, the modulus
  have nE : Emits cap (1 : Fin 3) rOP (fun _=>[]) (fun _=>WM.skip) 0 := emits_none cap
  have nL : EmitLen (fun _ : Bool=>([] : List Bool)) 0 := fun _=>by simp
  have pE : Emits cap (1 : Fin 3) rOP (fun b=>[true,b]) (fun b=>emitPair 1 rOP b) 15 := emits_pair cap
  have pL : EmitLen (fun b : Bool=>[true,b]) 2 := fun _=>by simp
  have rE : Emits cap (1 : Fin 3) rOP (fun b=>[b]) (fun b=>emitC 1 rOP b) 7 := emits_raw cap
  have rL : EmitLen (fun b : Bool=>[b]) 1 := fun _=>by simp
  have hWn : (natWord W0).length≤2*r.header.call.n+3 := by
    have:=NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le_self W0
    rw [hW0e] at this ⊢
    omega
  have hWl : (Streaming.marks (natWord W0)).length≤2*(2*r.header.call.n+3) := by
    rw [Streaming.marks_length];omega
  have e7:=framesCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=rOP) (SC:=rSX) (by decide) (by decide)
    nE nL (ctxFields r) n (wk++dg++q++T) σ6
    (by rw [t6_2,hIw,hC];simp [List.append_assoc]) g6_2 g6_1
    (by rw [u6OP,Nat.zero_mul];omega)
    (by rw [u6 rSX (by decide) (by decide) (by decide) (by decide) (by decide)];rw [←hC];omega)
  rw [←hC,flatMap_nil',show (ctxFields r).length=11 from rfl] at e7
  set σ7:=adv 2 1 rOP rSX σ6 [] C.length with hσ7
  have e8:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=rOP) (SC:=rSX) (K:=rK) (by decide) (by decide)
    (by decide) (by decide) nE nL r.walkCode.val (n++C) (dg++q++T) σ7
    (by rw [hσ7,adv_st_src (by decide),t6_2,hIw,hwk];simp [List.append_assoc])
    (by rw [hσ7,adv_sh_src,g6_2];simp)
    (by rw [hσ7,adv_sh_dst (by decide),adv_st_dst,g6_1];simp)
    (by rw [hσ7,adv_val_other _ _ _ rK (by decide) (by decide),
      u6 rK (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [hσ7,adv_val_OP (by decide),u6OP];simp only [List.length_nil,Nat.zero_mul];omega)
    (by rw [hσ7,adv_val_SC,u6 rSX (by decide) (by decide) (by decide) (by decide) (by decide),←hwk];omega)
    (by rw [←hwk];omega)
  rw [flatMap_nil',←hwk] at e8
  set σ8:=adv 2 1 rOP rSX σ7 [] wk.length with hσ8
  have σ8e : σ8=adv 2 1 rOP rSX σ6 [] (C.length+wk.length) := by
    rw [hσ8,hσ7,adv_adv (by decide) (by decide)];rfl
  have e9:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=rOP) (SC:=rSX) (K:=rK) (by decide) (by decide)
    (by decide) (by decide) nE nL r.degree (n++C++wk) (q++T) σ8
    (by rw [σ8e,adv_st_src (by decide),t6_2,hIw,hdg];simp [List.append_assoc])
    (by rw [σ8e,adv_sh_src,g6_2];simp only [List.length_append];omega)
    (by rw [σ8e,adv_sh_dst (by decide),adv_st_dst,g6_1];simp)
    (by rw [σ8e,adv_val_other _ _ _ rK (by decide) (by decide),
      u6 rK (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [σ8e,adv_val_OP (by decide),u6OP];simp only [List.length_nil,Nat.zero_mul];omega)
    (by rw [σ8e,adv_val_SC,u6 rSX (by decide) (by decide) (by decide) (by decide) (by decide),←hdg];omega)
    (by rw [←hdg];omega)
  rw [flatMap_nil',←hdg] at e9
  set σ9:=adv 2 1 rOP rSX σ8 [] dg.length with hσ9
  have σ9e : σ9=adv 2 1 rOP rSX σ6 [] (C.length+wk.length+dg.length) := by
    rw [hσ9,σ8e,adv_adv (by decide) (by decide)];rfl
  have e10:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=rOP) (SC:=rSX) (K:=rK) (by decide) (by decide)
    (by decide) (by decide) pE pL r.scale (n++C++wk++dg) T σ9
    (by rw [σ9e,adv_st_src (by decide),t6_2,hIw,←hq])
    (by rw [σ9e,adv_sh_src,g6_2];simp only [List.length_append];omega)
    (by rw [σ9e,adv_sh_dst (by decide),adv_st_dst,g6_1];simp)
    (by rw [σ9e,adv_val_other _ _ _ rK (by decide) (by decide),
      u6 rK (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [σ9e,adv_val_OP (by decide),u6OP,←hq];simp only [List.length_nil];omega)
    (by rw [σ9e,adv_val_SC,u6 rSX (by decide) (by decide) (by decide) (by decide) (by decide),←hq];omega)
    (by rw [←hq];omega)
  rw [flatMap_pair,←hq] at e10
  set σ10:=adv 2 1 rOP rSX σ9 (Streaming.marks q) q.length with hσ10
  have σ10e : σ10=adv 2 1 rOP rSX σ6 (Streaming.marks q) (C.length+wk.length+dg.length+q.length) := by
    rw [hσ10,σ9e,adv_adv (by decide) (by decide)];rfl
  -- rewind the input and copy the whole entry frame
  have e11:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (0 : Fin 3) rS0 (2*I.length+1) σ10
    (by rw [σ10e,adv_val_other _ _ _ rS0 (by decide) (by decide),u6S0])
    (by rw [σ10e,adv_val_other _ _ _ rS0 (by decide) (by decide),u6S0];omega)
  set σ11:=(σ10.setv rS0 0).seth 0 (σ10.sh 0-(2*I.length+1)) with hσ11
  have h10 : σ10.sh 0=2*I.length+1 := by
    rw [σ10e,adv_sh_other _ _ _ 0 (by decide) (by decide),g6_0]
  have e12:=frameCopy_spec cap (src:=(0 : Fin 3)) (dst:=1) (OP:=rOP) (SC:=rS0) (by decide) (by decide)
    rE rL I [] [] σ11
    (by simp only [hσ11,WState.seth_st,WState.setv_st,σ10e];rw [adv_st_other _ _ _ 0 (by decide),t6_0];simp)
    (by simp only [hσ11,WState.seth_sh,Function.update_self];rw [h10];simp)
    (by simp only [hσ11,WState.seth_sh,WState.setv_sh,WState.seth_st,WState.setv_st]
        rw [Function.update_of_ne (by decide),σ10e,adv_sh_dst (by decide),adv_st_dst,g6_1];simp)
    (by simp only [hσ11,WState.seth_val,WState.setv_val]
        rw [Function.update_of_ne (by decide),σ10e,adv_val_OP (by decide),u6OP]
        simp only [Streaming.marks_length,frame_length]
        rw [Streaming.marks_length] at hWl
        omega)
    (by simp only [hσ11,WState.seth_val,WState.setv_val,Function.update_self];simp [frame_length];omega)
  have o11 : σ11.st 1=Streaming.marks (natWord W0)++Streaming.marks q := by
    simp only [hσ11,WState.seth_st,WState.setv_st,σ10e,adv_st_dst,t6_1]
  refine ⟨_,WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 e12))))))))))) ?_,?_⟩
  · have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ r.header.call.n
    have hb2:=NearCubicGates.Close.Dispatch.natBitLength_le_succ W0
    have hW1 : W0≤r.header.call.n+1 := by rw [hW0e];omega
    have m1 : (natBitLength r.header.call.n+2)*(40*2^natBitLength r.header.call.n+40)≤
        (r.header.call.n+3)*(80*r.header.call.n+120) := Nat.mul_le_mul (by omega) (by omega)
    have m2 : (natBitLength W0+10)*(100*W0+200)≤(r.header.call.n+12)*(100*r.header.call.n+300) :=
      Nat.mul_le_mul (by omega) (by omega)
    have q1 : (natBitLength r.header.call.n+2)*(40*2^natBitLength r.header.call.n+40)≤
        400*(r.header.call.n+1)^2 := m1.trans (quad1 _)
    have q2 : (natBitLength W0+10)*(100*W0+200)≤3600*(r.header.call.n+1)^2 := m2.trans (quad2 _)
    have hN2 : r.header.call.n+1≤(r.header.call.n+1)^2 := Nat.le_self_pow (by decide) _
    simp only [frame_length,prefixCost]
    generalize (natBitLength r.header.call.n+2)*(40*2^natBitLength r.header.call.n+40)=P1 at q1 ⊢
    generalize (natBitLength W0+10)*(100*W0+200)=P2 at q2 ⊢
    generalize (r.header.call.n+1)^2=N2 at q1 q2 hN2 ⊢
    omega
  · rw [adv_st_dst,o11,flatMap_single,hq,frame_append_marks,Streaming.marks_append,hW0e]

/-- `lem:print` and `lem:residue`, paper/paper.tex:
the dense width and the actual binary modulus are retained in front of the unchanged entry word. -/
noncomputable def prefixWordFunction (B1 B2 : ℕ) :
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>(EntryFormat.ofGreedy r).word)
      (fun r=>frame (natWord ((r.source.child.call.n+1)/2)++natWord r.modulus++(EntryFormat.ofGreedy r).word))
      (fun r=>2*prefixCost (EntryFormat.ofGreedy r).word.length r.source.child.call.n+2) :=
  wordFunction_of_ideal (.wm prefixP) 1 (by decide)
    (fun r=>10*((EntryFormat.ofGreedy r).word.length+1)+8*(r.source.child.call.n+1)) (fun _ _=>0)
    (fun r=>prefixCost (EntryFormat.ofGreedy r).word.length r.source.child.call.n) (fun _=>le_rfl)
    (fun r=>⟨rfl,by
      obtain ⟨τ,he,ho⟩:=prefixP_run (EntryFormat.ofGreedy r)
      exact ⟨τ,WXExec.wm he,ho⟩⟩)

end NearQuarticWires.StageGreedyEntry
