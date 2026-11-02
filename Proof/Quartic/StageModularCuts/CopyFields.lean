import Proof.Quartic.StageModularCuts.KernelData
import Proof.Gates.CounterAsm.Copy

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterAsm
open NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: the affine fields
are copied byte-for-byte into the outer output frame. -/
def copyFields : WM 15 16 :=
  .whr 9 (.seq (.dec 9) (frameCopy 3 5 (fun b => emitPair 14 6 b)))

/-- `lem:print` and `prop:time`, paper/paper.tex: copying the affine fields is linear in their actual encoded
length and never decodes a signed coefficient magnitude. -/
theorem copyFields_spec (cap : ℕ) (fields : List (List Bool))
    (pre suffix : List Bool) (a : State)
    (hsource : a.st 3 = pre ++ fields.flatMap frame ++ suffix)
    (hhead : a.sh 3 = pre.length) (hout : a.sh 14 = (a.st 14).length)
    (hK : a.val 9 = fields.length)
    (hOP : a.val 6 + 2 * (fields.flatMap frame).length ≤ cap)
    (hsourceCap : a.val 5 + (fields.flatMap frame).length ≤ cap)
    (hcountCap : fields.length ≤ cap) :
    WExec cap copyFields a
      ((adv 3 14 6 5 a (marks (fields.flatMap frame)) (fields.flatMap frame).length).setv 9 0)
      (55 * (fields.flatMap frame).length + 4 * fields.length + 1) := by
  induction fields generalizing pre a with
  | nil =>
      have hzero : a.val 9 = 0 := hK
      simp only [List.flatMap_nil, List.length_nil, marks, adv_zero, Nat.mul_zero, Nat.zero_add]
      rw [show a.setv 9 0 = a by rw [← hzero]; exact wsetv_same a 9]
      exact WExec.whrF hzero
  | cons field fields ih =>
      have hbits : ((field :: fields).flatMap frame).length =
          (frame field).length + (fields.flatMap frame).length := by simp
      have eDec := WExec.dec (cap := cap) (9 : Fin 16) a
        (by simpa only [hK, List.length_cons] using hcountCap)
      let b := a.setv 9 fields.length
      have eDec' : WExec cap (.dec 9) a b 1 := by
        simpa only [hK, List.length_cons, Nat.add_sub_cancel] using eDec
      have eb := frameCopy_spec cap (by decide : (3 : Fin 16) ≠ 14)
        (by decide : (6 : Fin 16) ≠ 5) (emits_pair (cap := cap) (dst := (14 : Fin 16)) (OP := 6))
        (d := 2) (by intro bit; simp) field pre (fields.flatMap frame ++ suffix) b
        (by simpa only [b, WState.setv_st, List.flatMap_cons, List.append_assoc] using hsource)
        hhead hout
        (by simp only [b, WState.setv_val];
            rw [Function.update_of_ne (show (6 : Fin 16) ≠ 9 by decide)];
            rw [hbits] at hOP; omega)
        (by simp only [b, WState.setv_val];
            rw [Function.update_of_ne (show (5 : Fin 16) ≠ 9 by decide)];
            rw [hbits] at hsourceCap; omega)
      let c := adv 3 14 6 5 b (marks (frame field)) (frame field).length
      have eCopy : WExec cap (frameCopy 3 5 (fun bit => emitPair 14 6 bit)) b c
          (55 * (frame field).length) := by
        exact eb.mono (by omega)
      have hcsource : c.st 3 = (pre ++ frame field) ++ fields.flatMap frame ++ suffix := by
        rw [adv_st_src (by decide)]
        simpa only [b, WState.setv_st, List.flatMap_cons, List.append_assoc] using hsource
      have hchead : c.sh 3 = (pre ++ frame field).length := by
        rw [adv_sh_src]
        simpa only [b, WState.setv_sh, List.length_append] using
          congrArg (fun x => x + (frame field).length) hhead
      have hcout : c.sh 14 = (c.st 14).length := by
        rw [adv_sh_dst (by decide), adv_st_dst]
        simpa only [b, WState.setv_sh, WState.setv_st, List.length_append] using
          congrArg (fun x => x + (marks (frame field)).length) hout
      have hcK : c.val 9 = fields.length := by
        rw [adv_val_other _ _ _ (9 : Fin 16) (by decide) (by decide)]
        simp only [b, WState.setv_val, Function.update_self]
      have hcOP : c.val 6 + 2 * (fields.flatMap frame).length ≤ cap := by
        rw [adv_val_OP (by decide)]
        simp only [b, WState.setv_val, Streaming.marks_length]
        rw [Function.update_of_ne (show (6 : Fin 16) ≠ 9 by decide)]
        rw [hbits] at hOP
        omega
      have hcCap : c.val 5 + (fields.flatMap frame).length ≤ cap := by
        rw [adv_val_SC]
        simp only [b, WState.setv_val]
        rw [Function.update_of_ne (show (5 : Fin 16) ≠ 9 by decide)]
        rw [hbits] at hsourceCap
        omega
      have tail := ih (pre ++ frame field) c hcsource hchead hcout hcK hcOP hcCap
        (by simp only [List.length_cons] at hcountCap; omega)
      have whole := WExec.whrT (by rw [hK]; simp) (WExec.seq eDec' eCopy) tail
      refine WExec.mono (WExec.cast cap whole ?_ le_rfl) ?_
      · rw [show c = adv 3 14 6 5 b (marks (frame field)) (frame field).length from rfl,
          adv_adv (by decide) (by decide), show b = a.setv 9 fields.length from rfl,
          adv_setv _ _ _ (9 : Fin 16) _ (by decide) (by decide), wsetv_setv]
        simp only [List.flatMap_cons, List.length_append, Streaming.marks_append]
      · rw [hbits]
        simp only [List.length_cons]
        omega

end NearQuarticWires.StageModularCuts
