import Proof.Gates.CounterAsm.Copy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.CutScan

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a counted pass
consumes actual framed cut fields without decoding their magnitudes. -/
def skipFields (src : Fin (ns+1)) (SC K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (frameCopy src SC (fun _=>.skip)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the field pass advances its real cursor by exactly
the encoded fields and has linear cost in their bit length. -/
theorem skipFields_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (fields : List (List Bool)) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++fields.flatMap frame++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (hK : a.val K=fields.length)
    (hOP : a.val OP≤cap) (hsourceCap : a.val SC+(fields.flatMap frame).length≤cap)
    (hcountCap : fields.length≤cap) :
    WExec cap (skipFields src SC K) a
      ((adv src dst OP SC a [] (fields.flatMap frame).length).setv K 0)
      (25*(fields.flatMap frame).length+4*fields.length+1) := by
  induction fields generalizing pre a with
  | nil =>
      have hzero : a.val K=0 := hK
      simp only [List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,adv_zero]
      rw [show a.setv K 0=a by rw [←hzero];exact wsetv_same a K]
      exact WExec.whrF hzero
  | cons field fields ih =>
      have hbits : ((field::fields).flatMap frame).length=
          (frame field).length+(fields.flatMap frame).length := by simp
      have eDec:=WExec.dec (cap:=cap) K a (by simpa only [hK,List.length_cons] using hcountCap)
      let b:=a.setv K fields.length
      have eDec' : WExec cap (.dec K) a b 1 := by
        simpa only [hK,List.length_cons,Nat.add_sub_cancel] using eDec
      have eb:=frameCopy_spec cap hsd hOS (emits_none cap (dst:=dst) (OP:=OP))
        (show EmitLen (fun _ : Bool=>[]) 0 by intro x;rfl)
        field pre (fields.flatMap frame++suffix) b
        (by simpa only [b,WState.setv_st,List.flatMap_cons,List.append_assoc] using hsource)
        hhead hout (by simpa only [b,WState.setv_val,Function.update_of_ne hKO.symm,
          Nat.zero_mul,Nat.add_zero] using hOP)
        (by simp only [b,WState.setv_val,Function.update_of_ne hKS.symm];rw [hbits] at hsourceCap;omega)
      have eSkip : WExec cap (frameCopy src SC (fun _=>.skip)) b
          (adv src dst OP SC b [] (frame field).length) (25*(frame field).length) := by
        simpa only [List.flatMap_nil,List.flatMap_eq_nil_iff,Nat.mul_zero,Nat.zero_add,
          show (frame field).flatMap (fun _ : Bool=>[]) = [] by simp,Nat.mul_comm] using eb
      let c:=adv src dst OP SC b [] (frame field).length
      have hcsource : c.st src=(pre++frame field)++fields.flatMap frame++suffix := by
        rw [adv_st_src hsd]
        simpa only [b,WState.setv_st,List.flatMap_cons,List.append_assoc] using hsource
      have hchead : c.sh src=(pre++frame field).length := by
        rw [adv_sh_src]
        simpa only [b,WState.setv_sh,List.length_append] using
          congrArg (fun x=>x+(frame field).length) hhead
      have hcout : c.sh dst=(c.st dst).length := by
        rw [adv_sh_dst hsd,adv_st_dst]
        simpa only [b,WState.setv_sh,WState.setv_st,List.length_nil,Nat.add_zero,List.append_nil] using hout
      have hcK : c.val K=fields.length := by
        rw [adv_val_other _ _ _ K hKO hKS]
        simp only [b,WState.setv_val,Function.update_self]
      have hcOP : c.val OP≤cap := by
        rw [adv_val_OP hOS]
        simpa only [b,WState.setv_val,Function.update_of_ne hKO.symm,List.length_nil,Nat.add_zero] using hOP
      have hcCap : c.val SC+(fields.flatMap frame).length≤cap := by
        rw [adv_val_SC]
        simp only [b,WState.setv_val,Function.update_of_ne hKS.symm]
        rw [hbits] at hsourceCap
        omega
      have tail:=ih (pre++frame field) c hcsource hchead hcout hcK hcOP hcCap (by simp only [List.length_cons] at hcountCap;omega)
      have whole:=WExec.whrT (by rw [hK];simp) (WExec.seq eDec' eSkip) tail
      refine WExec.mono (WExec.cast cap whole ?_ le_rfl) ?_
      · rw [show c=adv src dst OP SC b [] (frame field).length from rfl,
          adv_adv hsd hOS,show b=a.setv K fields.length from rfl,
          adv_setv _ _ _ K _ hKO hKS,wsetv_setv]
        simp only [List.append_nil,List.flatMap_cons,List.length_append]
      · rw [hbits]
        simp only [List.length_cons]
        omega

end NearQuarticWires.StagePrint.CutScan
