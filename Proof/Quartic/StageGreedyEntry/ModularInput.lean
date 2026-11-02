import Proof.Quartic.StageGreedyEntry.Rows

/-!
# The literal modular-cut input after the equality-row call

Paper: `lem:residue` and `lem:print`, paper/paper.tex.

After the equality-row call, the retained naturals `a, b, c` (dense width, modulus, stack width) stand in
front of the signed weak stream `y`. `modInP` writes the modular-cut input
`Top.loadRec (natWord b) y (1^(c+1)) (1^a) [] … []` (`modInP_run`): the bits of the modulus field are
copied twice marked, the stream is framed in place, and the unary widths are written from the two
small decoded naturals. The modulus is never decoded.
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

/-- One bit at depth two. -/
def deep2 (b : Bool) : List Bool := [true,true,true,b]

theorem flatMap_deep2 : ∀ w : List Bool,w.flatMap deep2=Streaming.marks (Streaming.marks w)
  | []=>rfl
  | b::w=>by
    have h:=flatMap_deep2 w
    simp only [List.flatMap_cons,Streaming.marks,List.flatMap_append] at h ⊢
    rw [h];rfl

/-- `lem:residue`, `lem:certify`, paper/paper.tex: the physical program. -/
def modInP : WM 2 13 :=
  .seq (unframeP 0 2 qS0 qXO)
  (.seq (WM.rewind 2 qXO)
  (.seq (natCopy 2 qSX qK (fun _=>.skip))
  (.seq (natCopy 2 qSX qK (fun _=>.skip))
  (.seq (natCopy 2 qSX qK (fun _=>.skip))
  (.seq (addTo qSX qL qT)
  (.seq (addTo qSX qL qT)
  (.seq (WM.rewind 2 qSX)
  (.seq (readNatM false 2 qf qc qA qp qt)
  (.seq (natCopy 2 qSX qK (fun b=>emitList 1 qOP (deep2 b)))
  (.seq (emitList 1 qOP [true,false])
  (.seq (readNatM false 2 qf qc qC qp qt)
  (.seq (.inc qC)
  (.seq (WM.rewind 0 qS0)
  (.seq (cntLoop 0 qS0 qL (fun _=>.skip))
  (.seq (frameCopy 0 qS0 (fun b=>emitPair 1 qOP b))
  (.seq (unaryMarksP qC 1 qOP)
  (.seq (unaryMarksP qA 1 qOP)
    (emitList 1 qOP (emptyTail 7)))))))))))))))))))

/-- `prop:time`, paper/paper.tex: linear in the word, quadratic in the small widths. -/
def modInCost (L a c : ℕ) : ℕ := 1000*(L+1)+10^4*(a+c+2)^2

theorem modIn_output (a b c : ℕ) (y : List Bool) :
    frame (Top.loadRec (natWord b) y (List.replicate (c+1) true) (List.replicate a true) [] [] [] [] [] [] [])=
    (natWord b).flatMap deep2++[true,false]++Streaming.marks (frame y)++
      Streaming.marks (frame (List.replicate (c+1) true))++Streaming.marks (frame (List.replicate a true))++
      emptyTail 7 := by
  rw [flatMap_deep2,NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [Top.loadRec,Streaming.marks_append,emptyTail,List.append_assoc]
  rw [NearCubicGates.Close.Codec.frame_eq_marks (l:=[]),NearCubicGates.Close.Codec.frame_eq_marks (l:=natWord b)]
  simp [Streaming.marks,List.append_assoc]

theorem modIn_cost_arith (I A B C X L a c P1 P2 : ℕ) (hI : I=A+B+C+X) (hL : L=A+B+C)
    (q1 : P1≤400*(a+1)^2) (q2 : P2≤400*(c+1)^2) :
    24*I+9+1+(5*I+1+1+(A*(0+13)+1+(B*(0+13)+1+(C*(0+13)+1+(18*L+3+1+(18*L+3+1+(5*L+1+1+
      (P1+1+(B*(32+13)+1+(8*2+1+(P2+1+(3+1+(5*(2*I+1)+1+1+(2*L*(0+11)+1+1+((2*X+1)*(2*15+25)+1+
      (36*(c+1)+18+1+(36*a+18+1+8*15)))))))))))))))))≤1000*(I+1)+10^4*(a+c+2)^2 := by
  have s1 : (a+1)^2≤(a+c+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have s2 : (c+1)^2≤(a+c+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have s3 : a+c+2≤(a+c+2)^2 := Nat.le_self_pow (by decide) _
  subst hI hL
  generalize (a+1)^2=Na at q1 s1
  generalize (c+1)^2=Nc at q2 s2
  generalize (a+c+2)^2=N at s1 s2 s3 ⊢
  ring_nf
  omega

theorem modInP_run (a b c : ℕ) (y : List Bool) :
    ∃τ : WState 2 13,WExec (10*((natWord a++(natWord b++(natWord c++y))).length+1)+8*(a+c+4)) modInP
      (idealStart 2 13 (natWord a++(natWord b++(natWord c++y))) (fun _=>0)) τ
      (modInCost (natWord a++(natWord b++(natWord c++y))).length a c) ∧
      τ.st 1=frame (Top.loadRec (natWord b) y (List.replicate (c+1) true) (List.replicate a true)
        [] [] [] [] [] [] []) := by
  set I:=natWord a++(natWord b++(natWord c++y)) with hI
  set cap:=10*(I.length+1)+8*(a+c+4) with hcap
  obtain ⟨A,hA⟩ : ∃A,A=natWord a := ⟨_,rfl⟩
  obtain ⟨B,hB⟩ : ∃B,B=natWord b := ⟨_,rfl⟩
  obtain ⟨C,hC⟩ : ∃C,C=natWord c := ⟨_,rfl⟩
  have hIw : I=A++B++C++y := by rw [hI,hA,hB,hC];simp [List.append_assoc]
  have hlen : I.length=A.length+B.length+C.length+y.length := by rw [hIw];simp only [List.length_append]
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
  have dE : Emits cap (1 : Fin 3) qOP deep2 (fun b=>emitList 1 qOP (deep2 b)) 32 :=
    fun b τ ho hc=>emitList_exec cap 1 qOP (deep2 b) τ ho hc
  have dL : EmitLen deep2 4 := fun _=>le_refl _
  -- measure the three naturals
  have e3:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) nE nL a [] (B++C++y) σ2
    (by rw [t2,hIw,hA];simp [List.append_assoc]) (by rw [g2];rfl) (by rw [g1,t1];rfl)
    (u qK (by decide) (by decide)) (by rw [u qOP (by decide) (by decide)];omega)
    (by rw [u qSX (by decide) (by decide),←hA];omega) (by rw [←hA];omega)
  rw [flatMap_nil',←hA] at e3
  set σ3:=adv 2 1 qOP qSX σ2 [] A.length with hσ3
  have e4:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) nE nL b A (C++y) σ3
    (by rw [hσ3,adv_st_src (by decide),t2,hIw,hB];simp [List.append_assoc])
    (by rw [hσ3,adv_sh_src,g2];simp)
    (by rw [hσ3,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [hσ3,adv_val_other _ _ _ qK (by decide) (by decide),u qK (by decide) (by decide)])
    (by rw [hσ3,adv_val_OP (by decide),u qOP (by decide) (by decide)];simp)
    (by rw [hσ3,adv_val_SC,u qSX (by decide) (by decide),←hB];omega) (by rw [←hB];omega)
  rw [flatMap_nil',←hB] at e4
  set σ4:=adv 2 1 qOP qSX σ3 [] B.length with hσ4
  have σ4e : σ4=adv 2 1 qOP qSX σ2 [] (A.length+B.length) := by
    rw [hσ4,hσ3,adv_adv (by decide) (by decide)];rfl
  have e5:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) nE nL c (A++B) y σ4
    (by rw [σ4e,adv_st_src (by decide),t2,hIw,hC])
    (by rw [σ4e,adv_sh_src,g2];simp)
    (by rw [σ4e,adv_sh_dst (by decide),adv_st_dst,g1,t1];simp)
    (by rw [σ4e,adv_val_other _ _ _ qK (by decide) (by decide),u qK (by decide) (by decide)])
    (by rw [σ4e,adv_val_OP (by decide),u qOP (by decide) (by decide)];simp)
    (by rw [σ4e,adv_val_SC,u qSX (by decide) (by decide),←hC];omega) (by rw [←hC];omega)
  rw [flatMap_nil',←hC] at e5
  set σ5:=adv 2 1 qOP qSX σ4 [] C.length with hσ5
  have σ5e : σ5=adv 2 1 qOP qSX σ2 [] (A.length+B.length+C.length) := by
    rw [hσ5,σ4e,adv_adv (by decide) (by decide)];rfl
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
  have v8OP : σ8.val qOP=0 := by
    rw [v8 qOP (by decide) (by decide),σ5e,adv_val_OP (by decide),u qOP (by decide) (by decide)];rfl
  have t8_1 : σ8.st 1=[] := by
    simp only [hσ8,hσ7,hσ6,WState.seth_st,WState.setv_st];rw [σ5e,adv_st_dst,t1];rfl
  have g8_1 : σ8.sh 1=0 := by
    simp only [hσ8,hσ7,hσ6,WState.seth_sh,WState.setv_sh];rw [Function.update_of_ne (by decide),σ5e,
      adv_sh_dst (by decide),g1];rfl
  -- read the dense width, copy the modulus twice marked, read the stack width
  have hpa:=NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.two_pow_natBitLength_le a
  have e9:=readNatM_spec cap false (2 : Fin 3) qf qc qA qp qt
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) a [] (B++C++y) σ8
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
  have t9_1 : σ9.st 1=[] := by simp only [hσ9,WState.seth_st,WState.setv_st];exact t8_1
  have g9_1 : σ9.sh 1=(σ9.st 1).length := by
    rw [t9_1];simp only [hσ9,WState.setv_sh,WState.seth_sh];rw [Function.update_of_ne (by decide),g8_1];rfl
  have v9 (x : Fin 13) (h : x≠qA) : σ9.val x=σ8.val x := by
    simp only [hσ9,WState.setv_val,WState.seth_val];rw [Function.update_of_ne h]
  have v9A : σ9.val qA=a := by
    simp only [hσ9,WState.setv_val,Function.update_self]
    rw [z8 qA (by decide) (by decide) (by decide) (by decide) (by decide)];simp
  have e10:=natCopy_spec cap (src:=(2 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qSX) (K:=qK) (by decide) (by decide)
    (by decide) (by decide) dE dL b A (C++y) σ9
    (by rw [t9_2,hIw,hB];simp [List.append_assoc]) g9_2 g9_1
    (by rw [v9 qK (by decide),z8 qK (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v9 qOP (by decide),v8OP,←hB];omega)
    (by rw [v9 qSX (by decide),v8SX,←hB];omega) (by rw [←hB];omega)
  rw [←hB] at e10
  set σ10:=adv 2 1 qOP qSX σ9 (B.flatMap deep2) B.length with hσ10
  have hBd : (B.flatMap deep2).length=4*B.length := by
    rw [flatMap_deep2,Streaming.marks_length,Streaming.marks_length];ring
  have e11:=emitList_exec cap (1 : Fin 3) qOP [true,false] σ10
    (by rw [hσ10,adv_sh_dst (by decide),adv_st_dst,g9_1];simp)
    (by rw [hσ10,adv_val_OP (by decide),v9 qOP (by decide),v8OP,hBd];simp;omega)
  set σ11:=appendO σ10 1 qOP [true,false] with hσ11
  have v11 (x : Fin 13) (h1 : x≠qOP) (h2 : x≠qSX) : σ11.val x=σ9.val x := by
    simp only [hσ11,appendO_val];rw [Function.update_of_ne h1,hσ10,adv_val_other _ _ _ x h1 h2]
  have hpc:=NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.two_pow_natBitLength_le c
  have e12:=readNatM_spec cap false (2 : Fin 3) qf qc qC qp qt
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) c (A++B) y σ11
    (by simp only [hσ11,appendO_st];rw [Function.update_of_ne (by decide),hσ10,adv_st_src (by decide),t9_2,
        hIw,hC];simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
    (by simp only [hσ11,appendO_sh];rw [Function.update_of_ne (by decide),hσ10,adv_sh_src,g9_2];simp)
    (by rw [v11 qf (by decide) (by decide),v9 qf (by decide),
      z8 qf (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v11 qc (by decide) (by decide),v9 qc (by decide),
      z8 qc (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v11 qp (by decide) (by decide),v9 qp (by decide),
      z8 qp (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v11 qt (by decide) (by decide),v9 qt (by decide),
      z8 qt (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [v11 qC (by decide) (by decide),v9 qC (by decide),
      z8 qC (by decide) (by decide) (by decide) (by decide) (by decide),pow_succ];omega)
  set σ12:=(σ11.seth 2 ((A++B).length+NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false*
    (natWord c).length)).setv qC (σ11.val qC+c) with hσ12
  have v12C : σ12.val qC=c := by
    simp only [hσ12,WState.setv_val,Function.update_self]
    rw [v11 qC (by decide) (by decide),v9 qC (by decide),
      z8 qC (by decide) (by decide) (by decide) (by decide) (by decide)];simp
  have e13:=WExec.inc (cap:=cap) qC σ12 (by rw [v12C];omega)
  set σ13:=σ12.setv qC (σ12.val qC+1) with hσ13
  have v13 (x : Fin 13) (h1 : x≠qC) (h2 : x≠qOP) (h3 : x≠qSX) (h4 : x≠qA) : σ13.val x=σ8.val x := by
    simp only [hσ13,hσ12,WState.setv_val,WState.seth_val];rw [Function.update_of_ne h1,
      Function.update_of_ne h1,v11 x h2 h3,v9 x h4]
  have v13C : σ13.val qC=c+1 := by simp only [hσ13,WState.setv_val,Function.update_self];rw [v12C]
  have v13A : σ13.val qA=a := by
    simp only [hσ13,hσ12,WState.setv_val,WState.seth_val];rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide),v11 qA (by decide) (by decide),v9A]
  have v13OP : σ13.val qOP=4*B.length+2 := by
    simp only [hσ13,hσ12,WState.setv_val,WState.seth_val];rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide),hσ11,appendO_val,Function.update_self,hσ10,adv_val_OP (by decide),
      v9 qOP (by decide),v8OP,hBd];simp
  have v13L : σ13.val qL=2*L := by
    rw [v13 qL (by decide) (by decide) (by decide) (by decide),v8L]
  have v13S0 : σ13.val qS0=2*I.length+1 := by
    rw [v13 qS0 (by decide) (by decide) (by decide) (by decide),v8 qS0 (by decide) (by decide),σ5e,
      adv_val_other _ _ _ qS0 (by decide) (by decide),uS0]
  have t13_1 : σ13.st 1=B.flatMap deep2++[true,false] := by
    simp only [hσ13,hσ12,hσ11,WState.setv_st,WState.seth_st,appendO_st,Function.update_self]
    rw [hσ10,adv_st_dst,t9_1];simp
  have g13_1 : σ13.sh 1=(σ13.st 1).length := by
    rw [t13_1];simp only [hσ13,hσ12,hσ11,WState.setv_sh,WState.seth_sh,appendO_sh]
    rw [Function.update_of_ne (by decide),Function.update_self,hσ10,adv_sh_dst (by decide),g9_1,t9_1];simp
  have t13_0 : σ13.st 0=frame I := by
    simp only [hσ13,hσ12,hσ11,WState.setv_st,WState.seth_st,appendO_st]
    rw [Function.update_of_ne (by decide),hσ10,adv_st_other _ _ _ 0 (by decide)]
    simp only [hσ9,hσ8,hσ7,hσ6,WState.setv_st,WState.seth_st];rw [σ5e,adv_st_other _ _ _ 0 (by decide),t0]
  have g13_0 : σ13.sh 0=2*I.length+1 := by
    simp only [hσ13,hσ12,hσ11,WState.setv_sh,WState.seth_sh,appendO_sh]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide),hσ10,
      adv_sh_other _ _ _ 0 (by decide) (by decide)]
    simp only [hσ9,hσ8,hσ7,hσ6,WState.setv_sh,WState.seth_sh]
    rw [Function.update_of_ne (by decide),Function.update_of_ne (by decide),σ5e,
      adv_sh_other _ _ _ 0 (by decide) (by decide),g0]
  -- move the input head past the marked naturals and frame the stream in place
  have e14:=NearCubicWires.WireExponent3_5.FinalPass.Tm.wrewind_spec cap (0 : Fin 3) qS0 (2*I.length+1) σ13
    v13S0 (by rw [v13S0];omega)
  set σ14:=(σ13.setv qS0 0).seth 0 (σ13.sh 0-(2*I.length+1)) with hσ14
  have hw0 : frame I=Streaming.marks (A++B++C)++frame y := by
    rw [hIw,NearCubicGates.Close.Codec.frame_eq_marks,NearCubicGates.Close.Codec.frame_eq_marks,
      Streaming.marks_append];simp [List.append_assoc]
  have hwl : (Streaming.marks (A++B++C)).length=2*L := by
    rw [Streaming.marks_length];simp [hL];omega
  have e15:=cntLoop_spec cap (src:=(0 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qS0) (K:=qL) (by decide) (by decide)
    (by decide) (by decide) nE (frame y) (Streaming.marks (A++B++C)) [] σ14
    (by simp only [hσ14,WState.seth_st,WState.setv_st];rw [t13_0,hw0];simp)
    (by simp only [hσ14,WState.seth_sh,Function.update_self];rw [g13_0];simp)
    (by simp only [hσ14,WState.seth_sh,WState.setv_sh,WState.seth_st,WState.setv_st]
        rw [Function.update_of_ne (by decide),g13_1])
    (by simp only [hσ14,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v13L,hwl])
    (by rw [hwl];omega)
    (by simp only [hσ14,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v13OP];simp;omega)
    (by simp only [hσ14,WState.seth_val,WState.setv_val,Function.update_self];rw [hwl];omega)
  rw [flatMap_nil',hwl] at e15
  set σ15:=(adv 0 1 qOP qS0 σ14 [] (2*L)).setv qL 0 with hσ15
  have e16:=frameCopy_spec cap (src:=(0 : Fin 3)) (dst:=1) (OP:=qOP) (SC:=qS0) (by decide) (by decide)
    pE pL y (Streaming.marks (A++B++C)) [] σ15
    (by simp only [hσ15,WState.setv_st];rw [adv_st_src (by decide)]
        simp only [hσ14,WState.seth_st,WState.setv_st];rw [t13_0,hw0];simp)
    (by simp only [hσ15,WState.setv_sh];rw [adv_sh_src];simp only [hσ14,WState.seth_sh,Function.update_self]
        rw [g13_0,hwl];simp)
    (by simp only [hσ15,WState.setv_sh,WState.setv_st];rw [adv_sh_dst (by decide),adv_st_dst]
        simp only [hσ14,WState.seth_sh,WState.setv_sh,WState.seth_st,WState.setv_st]
        rw [Function.update_of_ne (by decide),g13_1];simp)
    (by simp only [hσ15,WState.setv_val];rw [Function.update_of_ne (by decide),adv_val_OP (by decide)]
        simp only [hσ14,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),v13OP]
        simp only [frame_length,List.length_nil];omega)
    (by simp only [hσ15,WState.setv_val];rw [Function.update_of_ne (by decide),adv_val_SC]
        simp only [hσ14,WState.seth_val,WState.setv_val,Function.update_self];simp only [frame_length];omega)
  rw [flatMap_pair] at e16
  set σ16:=adv 0 1 qOP qS0 σ15 (Streaming.marks (frame y)) (frame y).length with hσ16
  have t16_1 : σ16.st 1=B.flatMap deep2++[true,false]++Streaming.marks (frame y) := by
    rw [hσ16,adv_st_dst];simp only [hσ15,WState.setv_st];rw [adv_st_dst]
    simp only [hσ14,WState.seth_st,WState.setv_st];rw [t13_1];simp
  have g16_1 : σ16.sh 1=(σ16.st 1).length := by
    rw [hσ16,adv_sh_dst (by decide),adv_st_dst];simp only [hσ15,WState.setv_sh,WState.setv_st]
    rw [adv_sh_dst (by decide),adv_st_dst];simp only [hσ14,WState.seth_sh,WState.setv_sh,WState.seth_st,
      WState.setv_st];rw [Function.update_of_ne (by decide),g13_1];simp
  have v16 (x : Fin 13) (h1 : x≠qOP) (h2 : x≠qS0) (h3 : x≠qL) : σ16.val x=σ13.val x := by
    rw [hσ16,adv_val_other _ _ _ x h1 h2];simp only [hσ15,WState.setv_val];rw [Function.update_of_ne h3,
      adv_val_other _ _ _ x h1 h2];simp only [hσ14,WState.seth_val,WState.setv_val];rw [Function.update_of_ne h2]
  have v16OP : σ16.val qOP=4*B.length+2+2*(frame y).length := by
    rw [hσ16,adv_val_OP (by decide)];simp only [hσ15,WState.setv_val];rw [Function.update_of_ne (by decide),
      adv_val_OP (by decide)];simp only [hσ14,WState.seth_val,WState.setv_val];rw [Function.update_of_ne (by decide),
      v13OP];simp [Streaming.marks_length]
  -- the unary widths, the empty fields and the end marker
  have e17:=unaryMarks_exec cap qC (1 : Fin 3) qOP (by decide) (c+1) σ16
    (by rw [v16 qC (by decide) (by decide) (by decide),v13C]) (by omega) g16_1
    (by rw [v16OP];simp only [frame_length];omega)
  set σ17:=appendO (σ16.setv qC 0) 1 qOP (Streaming.marks (frame (List.replicate (c+1) true))) with hσ17
  have e18:=unaryMarks_exec cap qA (1 : Fin 3) qOP (by decide) a σ17
    (by simp only [hσ17,appendO_val,WState.setv_val];rw [Function.update_of_ne (by decide),
      Function.update_of_ne (by decide),v16 qA (by decide) (by decide) (by decide),v13A]) (by omega)
    (by simp [hσ17,g16_1])
    (by simp only [hσ17,appendO_val,WState.setv_val,Function.update_self];rw [Function.update_of_ne (by decide),
      v16OP,Streaming.marks_length];simp only [frame_length,List.length_replicate];omega)
  set σ18:=appendO (σ17.setv qA 0) 1 qOP (Streaming.marks (frame (List.replicate a true))) with hσ18
  have v18OP : σ18.val qOP=4*B.length+2+2*(frame y).length+
      (Streaming.marks (frame (List.replicate (c+1) true))).length+
      (Streaming.marks (frame (List.replicate a true))).length := by
    simp only [hσ18,hσ17,appendO_val,WState.setv_val,Function.update_self]
    rw [Function.update_of_ne (show qOP≠qA by decide),Function.update_self,
      Function.update_of_ne (show qOP≠qC by decide),v16OP]
  have hET : (emptyTail 7).length=15 := rfl
  have e19:=emitList_exec cap (1 : Fin 3) qOP (emptyTail 7) σ18 (by simp [hσ18,hσ17,g16_1];omega)
    (by rw [v18OP,hET,Streaming.marks_length,Streaming.marks_length]
        simp only [frame_length,List.length_replicate];rw [hcap];omega)
  refine ⟨_,WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 (WExec.seq e13
    (WExec.seq e14 (WExec.seq e15 (WExec.seq e16 (WExec.seq e17 (WExec.seq e18 e19)))))))))))))))))) ?_,?_⟩
  · have x6 : σ6.val qSX=L := by rw [v6 qSX (by decide),v5SX]
    rw [v5SX,x6]
    have hba:=NearCubicGates.Close.Dispatch.natBitLength_le_succ a
    have hbc:=NearCubicGates.Close.Dispatch.natBitLength_le_succ c
    have m1 : (natBitLength a+2)*(40*2^natBitLength a+40)≤(a+3)*(80*a+120) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m2 : (natBitLength c+2)*(40*2^natBitLength c+40)≤(c+3)*(80*c+120) :=
      Nat.mul_le_mul (by omega) (by omega)
    have q1:=m1.trans (quad1 a)
    have q2:=m2.trans (quad1 c)
    simp only [frame_length,modInCost,List.length_cons,List.length_nil]
    exact modIn_cost_arith I.length A.length B.length C.length y.length L a c _ _ hlen hL q1 q2
  · simp only [hσ18,hσ17,appendO_st,WState.setv_st,Function.update_self]
    rw [t16_1,modIn_output,hB]

end NearQuarticWires.StageGreedyEntry
