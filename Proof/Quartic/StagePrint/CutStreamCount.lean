import Proof.Quartic.StagePrint.CutRowCount

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.CutScan

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off0)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a row stream
has no additional delimiter between its actual framed fields. -/
def rowWord (fields : List (List Bool)) : List Bool := fields.flatMap frame

/-- `lem:print`, paper/paper.tex: count actual
equality rows at their frame boundaries before writing the native header. -/
def countRows (src : Fin (ns+1)) (R : Fin 6 ↪ Fin nr) : WM ns nr :=
  .whs src (countRow src R)

/-- `lem:print` and `prop:time`, paper/paper.tex: the source cursor and equality count are measured
by a physical pass, with linear dependence on the encoded cut stream. -/
theorem countRows_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 6 ↪ Fin nr)
    (hsd : src≠dst) (stride : ℕ) (rows : List (List (List Bool)))
    (hfields : ∀ row∈rows,row.length=stride)
    (hstarts : ∀ row∈rows,(rowWord row).headD false=true)
    (pre suffix : List Bool) (hsuffix : suffix.headD false=false) (a : WState ns nr)
    (hsource : a.st src=pre++rows.flatMap rowWord++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (hstride : a.val (R 2)=stride)
    (hK : a.val (R 3)=0) (hT : a.val (R 4)=0)
    (hOP : a.val (R 0)≤cap) (hsourceCap : a.val (R 1)+(rows.flatMap rowWord).length≤cap)
    (hstrideCap : stride≤cap) (hEQCap : a.val (R 5)+rows.length≤cap) :
    WExec cap (countRows src R) a
      ((adv src dst (R 0) (R 1) a [] (rows.flatMap rowWord).length).setv (R 5) (a.val (R 5)+rows.length))
      (25*(rows.flatMap rowWord).length+rows.length*(22*stride+11)+1) := by
  have ne : ∀ {i j : Fin 6},i≠j→R i≠R j := fun h=>R.injective.ne h
  induction rows generalizing pre a with
  | nil =>
      simp only [List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.zero_add,Nat.add_zero,adv_zero]
      rw [wsetv_same]
      refine WExec.whsF ?_
      unfold wbit
      rw [hsource,hhead]
      simp only [List.flatMap_nil,List.append_nil,rtb_off0]
      cases suffix with
      | nil=>rfl
      | cons b bs=>simpa only [readTapeBit,List.getD_cons_zero,List.headD_cons] using hsuffix
  | cons row rows ih =>
      have hlen : row.length=stride:=hfields row (by simp)
      have hbits : ((row::rows).flatMap rowWord).length=
          (rowWord row).length+(rows.flatMap rowWord).length := by simp
      have hbit : wbit a src=true := by
        unfold wbit
        rw [hsource,hhead]
        simp only [List.flatMap_cons,List.append_assoc,rtb_off0]
        have hs:=hstarts row (by simp)
        cases hw : rowWord row with
        | nil=>simp only [hw,List.headD_nil,Bool.false_eq_true] at hs
        | cons bit bits=>
            simpa only [hw,List.cons_append,readTapeBit,List.getD_cons_zero,List.headD_cons] using hs
      have eRow:=countRow_spec cap src dst R hsd row pre (rows.flatMap rowWord++suffix) a
        (by simpa only [List.flatMap_cons,List.append_assoc,rowWord] using hsource)
        hhead hout (hstride.trans hlen.symm) hK hT hOP
        (by rw [hbits] at hsourceCap;change a.val (R 1)+(rowWord row).length≤cap;omega)
        (by rw [hlen];exact hstrideCap)
        (by simp only [List.length_cons] at hEQCap;omega)
      let b:=(adv src dst (R 0) (R 1) a [] (rowWord row).length).setv (R 5) (a.val (R 5)+1)
      have hbsource : b.st src=(pre++rowWord row)++rows.flatMap rowWord++suffix := by
        rw [show b=(adv src dst (R 0) (R 1) a [] (rowWord row).length).setv (R 5) (a.val (R 5)+1) from rfl]
        simp only [WState.setv_st,adv_st_src hsd,hsource,List.flatMap_cons,List.append_assoc]
      have hbhead : b.sh src=(pre++rowWord row).length := by
        simp only [b,WState.setv_sh,adv_sh_src,hhead,List.length_append]
      have hbout : b.sh dst=(b.st dst).length := by
        simp only [b,WState.setv_sh,WState.setv_st,adv_sh_dst hsd,adv_st_dst,List.length_nil,Nat.add_zero,List.append_nil]
        exact hout
      have hbval (j : Fin 6) (hj : j≠5) (h0 : j≠0) (h1 : j≠1) : b.val (R j)=a.val (R j) := by
        simp only [b,WState.setv_val,Function.update_of_ne (ne hj)]
        exact adv_val_other _ _ _ (R j) (ne h0) (ne h1)
      have hbstride : b.val (R 2)=stride := (hbval 2 (by decide) (by decide) (by decide)).trans hstride
      have hbK : b.val (R 3)=0 := (hbval 3 (by decide) (by decide) (by decide)).trans hK
      have hbT : b.val (R 4)=0 := (hbval 4 (by decide) (by decide) (by decide)).trans hT
      have hbOP : b.val (R 0)≤cap := by
        simp only [b,WState.setv_val,Function.update_of_ne (ne (show (0:Fin 6)≠5 by decide)),
          adv_val_OP (ne (show (0:Fin 6)≠1 by decide)),List.length_nil,Nat.add_zero]
        exact hOP
      have hbSCap : b.val (R 1)+(rows.flatMap rowWord).length≤cap := by
        simp only [b,WState.setv_val,Function.update_of_ne (ne (show (1:Fin 6)≠5 by decide)),adv_val_SC]
        rw [hbits] at hsourceCap
        omega
      have hbEQ : b.val (R 5)+rows.length≤cap := by
        simp only [b,WState.setv_val,Function.update_self]
        simp only [List.length_cons] at hEQCap
        omega
      have tail:=ih (fun r hr=>hfields r (by simp [hr]))
        (fun r hr=>hstarts r (by simp [hr])) (pre++rowWord row) b
        hbsource hbhead hbout hbstride hbK hbT hbOP hbSCap hbEQ
      have whole:=WExec.whsT hbit eRow tail
      refine WExec.mono (WExec.cast cap whole ?_ le_rfl) ?_
      · rw [show b=(adv src dst (R 0) (R 1) a [] (rowWord row).length).setv (R 5) (a.val (R 5)+1) from rfl,
          adv_setv _ _ _ (R 5) _ (ne (by decide)) (ne (by decide)),adv_adv hsd (ne (by decide)),wsetv_setv]
        simp only [WState.setv_val,Function.update_self,List.flatMap_cons,List.length_append,List.length_cons,List.append_nil]
        congr 1
        omega
      · rw [hbits,hlen]
        change 25*(rowWord row).length+22*stride+9+2+
          (25*(rows.flatMap rowWord).length+rows.length*(22*stride+11)+1)≤_
        simp only [List.length_cons]
        nlinarith

end NearQuarticWires.StagePrint.CutScan
