import Proof.Quartic.StageGreedyEntry.StackWidth
import Proof.Quartic.StageGreedyEntry.Emit

/-!
# The literal equality-row input after the tuple call

Paper: `lem:print`, paper/paper.tex.

After the tuple call, the retained naturals `a, b, c` (dense width, modulus, stack width) stand in front
of the signed equality records `x`. `rowsP` copies the three naturals, reads the two small ones, frames
`x` in place and appends the unary width fields and eight empty fields of the equality-row input
`Top.loadRec x (1^a) (1^c) [] … []` (`rowsP_run`). The modulus is copied bit by bit, never decoded.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (addTo addTo_spec readNatM readNatM_spec)
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

def qOP : Fin 13 := 0
def qS0 : Fin 13 := 1
def qSX : Fin 13 := 2
def qK : Fin 13 := 3
def qXO : Fin 13 := 4
def qf : Fin 13 := 5
def qc : Fin 13 := 6
def qp : Fin 13 := 7
def qt : Fin 13 := 8
def qA : Fin 13 := 9
def qC : Fin 13 := 10
def qL : Fin 13 := 11
def qT : Fin 13 := 12

/-- The marked images of `k` empty frames, then the outer end marker. -/
def emptyTail (k : ℕ) : List Bool := (List.replicate k [true,false]).flatten++[false]

/-- `lem:print`, paper/paper.tex: the physical program. -/
def rowsP : WM 2 13 :=
  .seq (unframeP 0 2 qS0 qXO)
  (.seq (WM.rewind 2 qXO)
  (.seq (natCopy 2 qSX qK (fun b=>emitPair 1 qOP b))
  (.seq (natCopy 2 qSX qK (fun b=>emitPair 1 qOP b))
  (.seq (natCopy 2 qSX qK (fun b=>emitPair 1 qOP b))
  (.seq (addTo qSX qL qT)
  (.seq (addTo qSX qL qT)
  (.seq (WM.rewind 2 qSX)
  (.seq (readNatM false 2 qf qc qA qp qt)
  (.seq (natCopy 2 qSX qK (fun _=>.skip))
  (.seq (readNatM false 2 qf qc qC qp qt)
  (.seq (WM.rewind 0 qS0)
  (.seq (cntLoop 0 qS0 qL (fun _=>.skip))
  (.seq (frameCopy 0 qS0 (fun b=>emitPair 1 qOP b))
  (.seq (unaryMarksP qA 1 qOP)
  (.seq (unaryMarksP qC 1 qOP)
    (emitList 1 qOP (emptyTail 8)))))))))))))))))

/-- `prop:time`, paper/paper.tex: linear in the word, quadratic in the small widths. -/
def rowsCost (L a c : ℕ) : ℕ := 1000*(L+1)+10^4*(a+c+1)^2

theorem rows_output (a b c : ℕ) (x : List Bool) :
    frame (natWord a++(natWord b++(natWord c++
      Top.loadRec x (List.replicate a true) (List.replicate c true) [] [] [] [] [] [] [] [])))=
    Streaming.marks (natWord a)++Streaming.marks (natWord b)++Streaming.marks (natWord c)++
      Streaming.marks (frame x)++Streaming.marks (frame (List.replicate a true))++
      Streaming.marks (frame (List.replicate c true))++emptyTail 8 := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [Top.loadRec,Streaming.marks_append,emptyTail,List.append_assoc]
  rw [NearCubicGates.Close.Codec.frame_eq_marks (l:=[])]
  simp [Streaming.marks]

theorem rows_cost_arith (I A B C X L a c P1 P2 : ℕ) (hI : I=A+B+C+X) (hL : L=A+B+C)
    (q1 : P1≤400*(a+1)^2) (q2 : P2≤400*(c+1)^2) :
    24*I+9+1+(5*I+1+1+(A*(15+13)+1+(B*(15+13)+1+(C*(15+13)+1+(18*L+3+1+(18*L+3+1+(5*L+1+1+
      (P1+1+(B*(0+13)+1+(P2+1+(5*(2*I+1)+1+1+(2*L*(0+11)+1+1+((2*X+1)*(2*15+25)+1+
      (36*a+18+1+(36*c+18+1+8*17)))))))))))))))≤1000*(I+1)+10^4*(a+c+1)^2 := by
  have s1 : (a+1)^2≤(a+c+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have s2 : (c+1)^2≤(a+c+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have s3 : a+c+1≤(a+c+1)^2 := Nat.le_self_pow (by decide) _
  subst hI hL
  generalize (a+1)^2=Na at q1 s1
  generalize (c+1)^2=Nc at q2 s2
  generalize (a+c+1)^2=N at s1 s2 s3 ⊢
  norm_num at *
  omega


theorem rowsP_run (a b c : ℕ) (x : List Bool) :
    ∃τ : WState 2 13,WExec (10*((natWord a++(natWord b++(natWord c++x))).length+1)+8*(a+c+2)) rowsP
      (idealStart 2 13 (natWord a++(natWord b++(natWord c++x))) (fun _=>0)) τ
      (rowsCost (natWord a++(natWord b++(natWord c++x))).length a c) ∧
      τ.st 1=frame (natWord a++(natWord b++(natWord c++
        Top.loadRec x (List.replicate a true) (List.replicate c true) [] [] [] [] [] [] [] []))) := by
  set I:=natWord a++(natWord b++(natWord c++x)) with hI
  set cap:=10*(I.length+1)+8*(a+c+2) with hcap
  obtain ⟨A,hA⟩ : ∃A,A=natWord a := ⟨_,rfl⟩
  obtain ⟨B,hB⟩ : ∃B,B=natWord b := ⟨_,rfl⟩
  obtain ⟨C,hC⟩ : ∃C,C=natWord c := ⟨_,rfl⟩
  have hIw : I=A++B++C++x := by rw [hI,hA,hB,hC];simp [List.append_assoc]
  have hlen : I.length=A.length+B.length+C.length+x.length := by rw [hIw];simp only [List.length_append]
  set σ0:=idealStart 2 13 I (fun _=>0) with hσ0
  have s0 : σ0.st 0=frame I := by simp [hσ0,idealStart]
  have s1 : σ0.st 1=[] := by simp [hσ0,idealStart]
  have s2 : σ0.st 2=[] := by simp [hσ0,idealStart]
  have h0 (i : Fin 3) : σ0.sh i=0 := by simp [hσ0,idealStart]
  have v0 (x : Fin 13) : σ0.val x=0 := by simp [hσ0,idealStart]
  have e1:=unframe_spec cap (src:=0) (dst:=2) (OP:=qXO) (SC:=qS0) (by decide) (by decide) I [] [] σ0
    (by rw [s0];simp) (by rw [h0];rfl) (by rw [s2,h0];rfl) (by rw [v0];omega) (by rw [v0];omega)
  set σ1:=adv 0 2 qXO qS0 σ0 I (2*I.length+1) with hσ1
  have e2:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (2 : Fin 3) qXO I.length σ1
    (by rw [hσ1,adv_val_OP (by decide),v0];simp) (by rw [hσ1,adv_val_OP (by decide),v0];omega)
  set σ2:=(σ1.setv qXO 0).seth 2 (σ1.sh 2-I.length) with hσ2
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
  have u (x : Fin 13) (h1 : x≠qXO) (h2 : x≠qS0) : σ2.val x=0 := by
    simp only [hσ2,WState.seth_val,WState.setv_val,hσ1]
    rw [Function.update_of_ne h1,adv_val_other _ _ _ x h1 h2,v0]
  have uS0 : σ2.val qS0=2*I.length+1 := by
    simp only [hσ2,WState.seth_val,WState.setv_val,hσ1]
    rw [Function.update_of_ne (by decide),adv_val_SC,v0];simp
  have nE : Emits cap (1 : Fin 3) qOP (fun _=>[]) (fun _=>WM.skip) 0 := emits_none cap
  have nL : EmitLen (fun _ : Bool=>([] : List Bool)) 0 := fun _=>by simp
  have pE : Emits cap (1 : Fin 3) qOP (fun b=>[true,b]) (fun b=>emitPair 1 qOP b) 15 := emits_pair cap
  have pL : EmitLen (fun b : Bool=>[true,b]) 2 := fun _=>by simp
  -- copy the three naturals
  have e3:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) pE pL a [] (B++C++x) σ2
    (by rw [t2,hIw,hA];simp [List.append_assoc]) (by rw [g2];rfl) (by rw [g1,t1];rfl)
    (u qK (by decide) (by decide)) (by rw [u qOP (by decide) (by decide),←hA];omega)
    (by rw [u qSX (by decide) (by decide),←hA];omega) (by rw [←hA];omega)
  rw [flatMap_pair,←hA] at e3
  set σ3:=adv 2 1 qOP qSX σ2 (Streaming.marks A) A.length with hσ3
  have e4:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) pE pL b A (C++x) σ3
    (by rw [hσ3,adv_st_src (by decide),t2,hIw,hB];simp [List.append_assoc])
    (by rw [hσ3,adv_sh_src,g2];simp)
    (by rw [hσ3,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [hσ3,adv_val_other _ _ _ qK (by decide) (by decide),u qK (by decide) (by decide)])
    (by rw [hσ3,adv_val_OP (by decide),u qOP (by decide) (by decide),←hB,Streaming.marks_length];omega)
    (by rw [hσ3,adv_val_SC,u qSX (by decide) (by decide),←hB];omega) (by rw [←hB];omega)
  rw [flatMap_pair,←hB] at e4
  set σ4:=adv 2 1 qOP qSX σ3 (Streaming.marks B) B.length with hσ4
  have σ4e : σ4=adv 2 1 qOP qSX σ2 (Streaming.marks A++Streaming.marks B) (A.length+B.length) := by
    rw [hσ4,hσ3,adv_adv (by decide) (by decide)]
  have e5:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) pE pL c (A++B) x σ4
    (by rw [σ4e,adv_st_src (by decide),t2,hIw,hC])
    (by rw [σ4e,adv_sh_src,g2];simp)
    (by rw [σ4e,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [σ4e,adv_val_other _ _ _ qK (by decide) (by decide),u qK (by decide) (by decide)])
    (by rw [σ4e,adv_val_OP (by decide),u qOP (by decide) (by decide),←hC];simp;omega)
    (by rw [σ4e,adv_val_SC,u qSX (by decide) (by decide),←hC];omega) (by rw [←hC];omega)
  rw [flatMap_pair,←hC] at e5
  set σ5:=adv 2 1 qOP qSX σ4 (Streaming.marks C) C.length with hσ5
  have σ5e : σ5=adv 2 1 qOP qSX σ2 (Streaming.marks A++Streaming.marks B++Streaming.marks C)
      (A.length+B.length+C.length) := by
    rw [hσ5,σ4e,adv_adv (by decide) (by decide)]
  set L:=A.length+B.length+C.length with hL
  have v5SX : σ5.val qSX=L := by rw [σ5e,adv_val_SC,u qSX (by decide) (by decide)];simp
  have v5 (x : Fin 13) (h1 : x≠qXO) (h2 : x≠qS0) (h3 : x≠qOP) (h4 : x≠qSX) : σ5.val x=0 := by
    rw [σ5e,adv_val_other _ _ _ x h3 h4,u x h1 h2]
  -- twice the prefix length
  have e6:=addTo_spec cap qSX qL qT (by decide) (by decide) (by decide) σ5
    (v5 qT (by decide) (by decide) (by decide) (by decide)) (by rw [v5SX];omega)
    (by rw [v5SX,v5 qL (by decide) (by decide) (by decide) (by decide)];omega)
  set σ6:=σ5.setv qL (σ5.val qL+σ5.val qSX) with hσ6
  have v6 (x : Fin 13) (h : x≠qL) : σ6.val x=σ5.val x := by
    simp only [hσ6,WState.setv_val];rw [Function.update_of_ne h]
  have v6L : σ6.val qL=L := by
    simp only [hσ6,WState.setv_val,Function.update_self]
    rw [v5SX,v5 qL (by decide) (by decide) (by decide) (by decide)];omega
  have e7:=addTo_spec cap qSX qL qT (by decide) (by decide) (by decide) σ6
    (by rw [v6 qT (by decide),v5 qT (by decide) (by decide) (by decide) (by decide)])
    (by rw [v6 qSX (by decide),v5SX];omega)
    (by rw [v6 qSX (by decide),v5SX,v6L];omega)
  set σ7:=σ6.setv qL (σ6.val qL+σ6.val qSX) with hσ7
  have v7 (x : Fin 13) (h : x≠qL) : σ7.val x=σ5.val x := by
    simp only [hσ7,WState.setv_val];rw [Function.update_of_ne h,v6 x h]
  have v7L : σ7.val qL=2*L := by
    simp only [hσ7,WState.setv_val,Function.update_self]
    rw [v6 qSX (by decide),v5SX,v6L];omega
  -- rewind the decoded copy, read the two small naturals
  have e8:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (2 : Fin 3) qSX L σ7
    (by rw [v7 qSX (by decide),v5SX]) (by rw [v7 qSX (by decide),v5SX];omega)
  set σ8:=(σ7.setv qSX 0).seth 2 (σ7.sh 2-L) with hσ8
  have g7_2 : σ7.sh 2=L := by
    simp only [hσ7,hσ6,WState.setv_sh];rw [σ5e,adv_sh_src,g2];simp [hL]
  have t8_2 : σ8.st 2=I := by
    simp only [hσ8,hσ7,hσ6,WState.seth_st,WState.setv_st];rw [σ5e,adv_st_src (by decide),t2]
  have g8_2 : σ8.sh 2=0 := by simp [hσ8,g7_2]
  have v8 (x : Fin 13) (h1 : x≠qSX) (h2 : x≠qL) : σ8.val x=σ5.val x := by
    simp only [hσ8,WState.seth_val,WState.setv_val];rw [Function.update_of_ne h1,v7 x h2]
  have v8L : σ8.val qL=2*L := by
    simp only [hσ8,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v7L]
  have v8SX : σ8.val qSX=0 := by simp [hσ8]
  have z8 (x : Fin 13) (h1 : x≠qSX) (h2 : x≠qL) (h3 : x≠qXO) (h4 : x≠qS0) (h5 : x≠qOP) : σ8.val x=0 := by
    rw [v8 x h1 h2,v5 x h3 h4 h5 h1]
  have hpa:=NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.two_pow_natBitLength_le a
  have e9:=readNatM_spec cap false (2 : Fin 3) qf qc qA qp qt
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a [] (B++C++x) σ8
    (by rw [t8_2,hIw,hA];simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,List.append_assoc])
    (by rw [g8_2];rfl)
    (z8 qf (by decide) (by decide) (by decide) (by decide) (by decide))
    (z8 qc (by decide) (by decide) (by decide) (by decide) (by decide))
    (z8 qp (by decide) (by decide) (by decide) (by decide) (by decide))
    (z8 qt (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [z8 qA (by decide) (by decide) (by decide) (by decide) (by decide),pow_succ];omega)
  set σ9:=(σ8.seth 2 ([].length+NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false*
    (natWord a).length)).setv qA (σ8.val qA+a) with hσ9
  have t9_2 : σ9.st 2=I := by simp [hσ9,t8_2]
  have g9_2 : σ9.sh 2=A.length := by
    simp [hσ9,hA,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]
  have t9_1 : σ9.st 1=Streaming.marks A++Streaming.marks B++Streaming.marks C := by
    simp only [hσ9,hσ8,hσ7,hσ6,WState.seth_st,WState.setv_st];rw [σ5e,adv_st_dst,t1];simp
  have g9_1 : σ9.sh 1=(σ9.st 1).length := by
    rw [t9_1];simp only [hσ9,hσ8,hσ7,hσ6,WState.seth_sh,WState.setv_sh]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide),σ5e,adv_sh_dst (by decide),g1]
    simp [Streaming.marks_length]
  have v9 (x : Fin 13) (h : x≠qA) : σ9.val x=σ8.val x := by
    simp only [hσ9,WState.setv_val,WState.seth_val];rw [Function.update_of_ne h]
  have v9A : σ9.val qA=a := by
    simp only [hσ9,WState.setv_val,Function.update_self]
    rw [z8 qA (by decide) (by decide) (by decide) (by decide) (by decide)];simp
  have v5OP : σ5.val qOP=2*L := by
    rw [σ5e,adv_val_OP (by decide),u qOP (by decide) (by decide)];simp [Streaming.marks_length,hL];ring
  have e10:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) nE nL b A (C++x) σ9
    (by rw [t9_2,hIw,hB];simp [List.append_assoc]) g9_2 g9_1
    (by rw [v9 qK (by decide),z8 qK (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v9 qOP (by decide),v8 qOP (by decide) (by decide),v5OP];simp;omega)
    (by rw [v9 qSX (by decide),v8SX,←hB];omega) (by rw [←hB];omega)
  rw [flatMap_nil',←hB] at e10
  set σ10:=adv 2 1 qOP qSX σ9 [] B.length with hσ10
  have hpc:=NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.two_pow_natBitLength_le c
  have v10 (x : Fin 13) (h1 : x≠qOP) (h2 : x≠qSX) : σ10.val x=σ9.val x := by
    rw [hσ10,adv_val_other _ _ _ x h1 h2]
  have e11:=readNatM_spec cap false (2 : Fin 3) qf qc qC qp qt
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) c (A++B) x σ10
    (by rw [hσ10,adv_st_src (by decide),t9_2,hIw,hC];simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
    (by rw [hσ10,adv_sh_src,g9_2];simp)
    (by rw [v10 qf (by decide) (by decide),v9 qf (by decide),
      z8 qf (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v10 qc (by decide) (by decide),v9 qc (by decide),
      z8 qc (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v10 qp (by decide) (by decide),v9 qp (by decide),
      z8 qp (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v10 qt (by decide) (by decide),v9 qt (by decide),
      z8 qt (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v10 qC (by decide) (by decide),v9 qC (by decide),
      z8 qC (by decide) (by decide) (by decide) (by decide) (by decide),pow_succ];omega)
  set σ11:=(σ10.seth 2 ((A++B).length+NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false*
    (natWord c).length)).setv qC (σ10.val qC+c) with hσ11
  have v11 (x : Fin 13) (h1 : x≠qC) (h2 : x≠qOP) (h3 : x≠qSX) (h4 : x≠qA) : σ11.val x=σ8.val x := by
    simp only [hσ11,WState.setv_val,WState.seth_val];rw [Function.update_of_ne h1,v10 x h2 h3,v9 x h4]
  have v11C : σ11.val qC=c := by
    simp only [hσ11,WState.setv_val,Function.update_self]
    rw [v10 qC (by decide) (by decide),v9 qC (by decide),
      z8 qC (by decide) (by decide) (by decide) (by decide) (by decide)];simp
  have v11A : σ11.val qA=a := by
    simp only [hσ11,WState.setv_val,WState.seth_val];rw [Function.update_of_ne (by decide),
      v10 qA (by decide) (by decide),v9A]
  have v11OP : σ11.val qOP=2*L := by
    simp only [hσ11,WState.setv_val,WState.seth_val];rw [Function.update_of_ne (by decide),hσ10,
      adv_val_OP (by decide),v9 qOP (by decide),v8 qOP (by decide) (by decide),v5OP];simp
  have v11L : σ11.val qL=2*L := by
    rw [v11 qL (by decide) (by decide) (by decide) (by decide),v8L]
  have v11S0 : σ11.val qS0=2*I.length+1 := by
    rw [v11 qS0 (by decide) (by decide) (by decide) (by decide),v8 qS0 (by decide) (by decide),σ5e,
      adv_val_other _ _ _ qS0 (by decide) (by decide),uS0]
  have t11_1 : σ11.st 1=Streaming.marks A++Streaming.marks B++Streaming.marks C := by
    simp only [hσ11,WState.setv_st,WState.seth_st,hσ10];rw [adv_st_dst,t9_1];simp
  have g11_1 : σ11.sh 1=(σ11.st 1).length := by
    simp only [hσ11,WState.setv_sh,WState.seth_sh,WState.setv_st,WState.seth_st]
    rw [Function.update_of_ne (by decide),hσ10,adv_sh_dst (by decide),adv_st_dst,g9_1];simp
  have t11_0 : σ11.st 0=frame I := by
    simp only [hσ11,WState.setv_st,WState.seth_st,hσ10];rw [adv_st_other _ _ _ 0 (by decide)]
    simp only [hσ9,hσ8,hσ7,hσ6,WState.setv_st,WState.seth_st];rw [σ5e,adv_st_other _ _ _ 0 (by decide),t0]
  have g11_0 : σ11.sh 0=2*I.length+1 := by
    simp only [hσ11,WState.setv_sh,WState.seth_sh];rw [Function.update_of_ne (by decide),hσ10,
      adv_sh_other _ _ _ 0 (by decide) (by decide)]
    simp only [hσ9,hσ8,hσ7,hσ6,WState.setv_sh,WState.seth_sh]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide),σ5e,
      adv_sh_other _ _ _ 0 (by decide) (by decide),g0]
  -- move the input head past the marked naturals and frame the records in place
  have e12:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (0 : Fin 3) qS0 (2*I.length+1) σ11
    v11S0 (by rw [v11S0];omega)
  set σ12:=(σ11.setv qS0 0).seth 0 (σ11.sh 0-(2*I.length+1)) with hσ12
  have hw0 : frame I=Streaming.marks (A++B++C)++frame x := by
    rw [hIw,NearCubicGates.Close.Codec.frame_eq_marks,NearCubicGates.Close.Codec.frame_eq_marks,
      Streaming.marks_append];simp [List.append_assoc]
  have hwl : (Streaming.marks (A++B++C)).length=2*L := by
    rw [Streaming.marks_length];simp [hL];omega
  have e13:=cntLoop_spec cap (src:=(0 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qS0) (K:=qL) (by decide) (by decide)
    (by decide) (by decide) nE (frame x) (Streaming.marks (A++B++C)) [] σ12
    (by simp only [hσ12,WState.seth_st,WState.setv_st];rw [t11_0,hw0];simp)
    (by simp only [hσ12,WState.seth_sh,Function.update_self];rw [g11_0];simp)
    (by simp only [hσ12,WState.seth_sh,WState.setv_sh,WState.seth_st,WState.setv_st]
        rw [Function.update_of_ne (by decide),g11_1])
    (by simp only [hσ12,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v11L,hwl])
    (by rw [hwl];omega)
    (by simp only [hσ12,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v11OP];simp;omega)
    (by simp only [hσ12,WState.seth_val,WState.setv_val,Function.update_self];rw [hwl];omega)
  rw [flatMap_nil',hwl] at e13
  set σ13:=(adv 0 1 qOP qS0 σ12 [] (2*L)).setv qL 0 with hσ13
  have e14:=frameCopy_spec cap (src:=(0 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qS0) (by decide) (by decide)
    pE pL x (Streaming.marks (A++B++C)) [] σ13
    (by simp only [hσ13,WState.setv_st];rw [adv_st_src (by decide)]
        simp only [hσ12,WState.seth_st,WState.setv_st];rw [t11_0,hw0];simp)
    (by simp only [hσ13,WState.setv_sh];rw [adv_sh_src];simp only [hσ12,WState.seth_sh,Function.update_self]
        rw [g11_0,hwl];simp)
    (by simp only [hσ13,WState.setv_sh,WState.setv_st];rw [adv_sh_dst (by decide),adv_st_dst]
        simp only [hσ12,WState.seth_sh,WState.setv_sh,WState.seth_st,WState.setv_st]
        rw [Function.update_of_ne (by decide),g11_1];simp)
    (by simp only [hσ13,WState.setv_val];rw [Function.update_of_ne (by decide),adv_val_OP (by decide)]
        simp only [hσ12,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v11OP]
        simp only [frame_length,List.length_nil];omega)
    (by simp only [hσ13,WState.setv_val];rw [Function.update_of_ne (by decide),adv_val_SC]
        simp only [hσ12,WState.seth_val,WState.setv_val,Function.update_self];simp only [frame_length];omega)
  rw [flatMap_pair] at e14
  set σ14:=adv 0 1 qOP qS0 σ13 (Streaming.marks (frame x)) (frame x).length with hσ14
  have t14_1 : σ14.st 1=Streaming.marks A++Streaming.marks B++Streaming.marks C++Streaming.marks (frame x) := by
    rw [hσ14,adv_st_dst];simp only [hσ13,WState.setv_st];rw [adv_st_dst]
    simp only [hσ12,WState.seth_st,WState.setv_st];rw [t11_1];simp
  have g14_1 : σ14.sh 1=(σ14.st 1).length := by
    rw [hσ14,adv_sh_dst (by decide),adv_st_dst];simp only [hσ13,WState.setv_sh,WState.setv_st]
    rw [adv_sh_dst (by decide),adv_st_dst];simp only [hσ12,WState.seth_sh,WState.setv_sh,WState.seth_st,
      WState.setv_st];rw [Function.update_of_ne (by decide),g11_1];simp
  have v14 (x : Fin 13) (h1 : x≠qOP) (h2 : x≠qS0) (h3 : x≠qL) : σ14.val x=σ11.val x := by
    rw [hσ14,adv_val_other _ _ _ x h1 h2];simp only [hσ13,WState.setv_val];rw [Function.update_of_ne h3,
      adv_val_other _ _ _ x h1 h2];simp only [hσ12,WState.seth_val,WState.setv_val];rw [Function.update_of_ne h2]
  have v14OP : σ14.val qOP=2*L+2*(frame x).length := by
    rw [hσ14,adv_val_OP (by decide)];simp only [hσ13,WState.setv_val];rw [Function.update_of_ne (by decide),
      adv_val_OP (by decide)];simp only [hσ12,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),
      v11OP];simp [Streaming.marks_length]
  -- the unary widths, the empty fields and the end marker
  have e15:=unaryMarks_exec cap qA (1 : Fin 3) qOP (by decide) a σ14
    (by rw [v14 qA (by decide) (by decide) (by decide),v11A]) (by omega) g14_1
    (by rw [v14OP];simp only [frame_length];omega)
  set σ15:=appendO (σ14.setv qA 0) 1 qOP (Streaming.marks (frame (List.replicate a true))) with hσ15
  have e16:=unaryMarks_exec cap qC (1 : Fin 3) qOP (by decide) c σ15
    (by simp only [hσ15,appendO_val,WState.setv_val];rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide),v14 qC (by decide) (by decide) (by decide),v11C]) (by omega)
    (by simp [hσ15,g14_1])
    (by simp only [hσ15,appendO_val,WState.setv_val,Function.update_self];rw [Function.update_of_ne (by decide),
      v14OP,Streaming.marks_length];simp only [frame_length,List.length_replicate];omega)
  set σ16:=appendO (σ15.setv qC 0) 1 qOP (Streaming.marks (frame (List.replicate c true))) with hσ16
  have v16OP : σ16.val qOP=2*L+2*(frame x).length+(Streaming.marks (frame (List.replicate a true))).length+
      (Streaming.marks (frame (List.replicate c true))).length := by
    simp only [hσ16,hσ15,appendO_val,WState.setv_val,Function.update_self]
    rw [Function.update_of_ne (show qOP≠qC by decide),Function.update_self,
      Function.update_of_ne (show qOP≠qA by decide),v14OP]
  have hET : (emptyTail 8).length=17 := rfl
  have e17:=emitList_exec cap (1 : Fin 3) qOP (emptyTail 8) σ16 (by simp [hσ16,hσ15,g14_1];omega)
    (by rw [v16OP,hET,Streaming.marks_length,Streaming.marks_length]
        simp only [frame_length,List.length_replicate];omega)
  refine ⟨_,WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 (WExec.seq e13
    (WExec.seq e14 (WExec.seq e15 (WExec.seq e16 e17)))))))))))))))) ?_,?_⟩
  · have hba:=NearCubicGates.Close.Dispatch.natBitLength_le_succ a
    have hbc:=NearCubicGates.Close.Dispatch.natBitLength_le_succ c
    have m1 : (natBitLength a+2)*(40*2^natBitLength a+40)≤(a+3)*(80*a+120) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m2 : (natBitLength c+2)*(40*2^natBitLength c+40)≤(c+3)*(80*c+120) :=
      Nat.mul_le_mul (by omega) (by omega)
    have q1:=m1.trans (quad1 a)
    have q2:=m2.trans (quad1 c)
    have x6 : σ6.val qSX=L := by rw [v6 qSX (by decide),v5SX]
    rw [v5SX,x6]
    simp only [frame_length,rowsCost,hET]
    exact rows_cost_arith I.length A.length B.length C.length x.length L a c _ _ hlen hL q1 q2
  · simp only [hσ16,hσ15,appendO_st,WState.setv_st,Function.update_self]
    rw [t14_1,rows_output,hA,hB,hC]

end NearQuarticWires.StageGreedyEntry
