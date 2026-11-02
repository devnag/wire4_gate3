import Proof.Quartic.StagePrintTuple.PayloadCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off0)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the number of
ORIGINAL compiler children is counted from the actual framed child
records, rather than supplied as an output-count field. -/
def countChildFrames (src : Fin (ns+1)) (SC K : Fin nr) : WM ns nr :=
  .whs src (.seq (CounterAsm.frameCopy src SC (fun _=>WM.skip)) (.inc K))

/-- `lem:print` and `prop:time`, paper/paper.tex: one marker/data scan counts every actual nonempty
child record exactly once, preserves its source bits, and records the
actual scanned byte length for a later physical rewind. -/
theorem countChildFrames_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (rest : List Bool) (hend : rest.headD false=false) :
    ∀ (records : List (List Bool)) (pre : List Bool) (σ : WState ns nr),
      (∀ record∈records,record≠[]) →
      σ.st src=pre++records.flatMap frame++rest → σ.sh src=pre.length →
      σ.sh dst=(σ.st dst).length → σ.val OP≤cap →
      σ.val SC+(records.flatMap frame).length≤cap →
      σ.val K+records.length≤cap →
      WExec cap (countChildFrames src SC K) σ
        ((adv src dst OP SC σ [] (records.flatMap frame).length).setv K
          (σ.val K+records.length))
        (40*(records.flatMap frame).length+10*records.length+1) := by
  intro records
  induction records with
  | nil =>
    intro pre σ _hne hs hh _hd _ho _hsc _hk
    have hw : wbit σ src=false := by
      unfold wbit
      rw [hs,hh]
      simp only [List.flatMap_nil,List.append_nil,rtb_off0]
      cases rest with
      | nil => rfl
      | cons b rest => simp only [List.headD_cons] at hend;subst b;rfl
    simpa only [countChildFrames,List.flatMap_nil,List.length_nil,Nat.add_zero,
      Nat.mul_zero,Nat.zero_add,adv_zero,wsetv_same] using (WExec.whsF (cap:=cap) hw)
  | cons record records ih =>
    intro pre σ hne hs hh hd ho hsc hk
    have hlen : ((record::records).flatMap frame).length=
      (frame record).length+(records.flatMap frame).length := by simp
    have hw : wbit σ src=true := by
      obtain ⟨tail,ht⟩ := CounterAsm.frame_cons (hne record (by simp))
      unfold wbit
      rw [hs,hh]
      simp only [List.flatMap_cons,List.append_assoc,rtb_off0,ht]
      rfl
    have e1 := CounterAsm.frameCopy_spec cap hsd hOS
      (emits_none (cap:=cap) (dst:=dst) (OP:=OP)) (d:=0) (by intro b;simp)
      record pre (records.flatMap frame++rest) σ
      (by simpa only [List.flatMap_cons,List.append_assoc] using hs) hh hd
      (by simpa using ho) (by rw [hlen] at hsc;omega)
    have hzero : (frame record).flatMap (fun _=> ([] : List Bool))=[] := by simp
    rw [hzero] at e1
    let d := adv src dst OP SC σ [] (frame record).length
    have dk : d.val K=σ.val K := adv_val_other _ _ _ K hKO hKS
    have e2 := WExec.inc (cap:=cap) K d (by rw [dk];simp only [List.length_cons] at hk;omega)
    let e := d.setv K (d.val K+1)
    have et := ih (pre++frame record) e (fun x hx=>hne x (by simp [hx]))
      (by simp only [e,WState.setv_st,d,adv_st_src hsd];rw [hs]
          simp only [List.flatMap_cons,List.append_assoc])
      (by simp [e,d,adv_sh_src,hh])
      (by simp [e,d,adv,appendO,hsd.symm,hd])
      (by simp [e,d,adv,appendO,hKO.symm,hOS];exact ho)
      (by simp only [e,WState.setv_val,Function.update_of_ne hKS.symm,d,adv_val_SC]
          rw [hlen] at hsc;omega)
      (by simp only [e,WState.setv_val,Function.update_self,dk,List.length_cons] at *;omega)
    refine (WExec.whsT hw (e1.seq e2) et).cast cap ?_ (by
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega)
    rw [show e=d.setv K (d.val K+1) from rfl,adv_setv _ _ _ K _ hKO hKS,
      show d=adv src dst OP SC σ [] (frame record).length from rfl,
      adv_adv hsd hOS,wsetv_setv]
    simp only [WState.setv_val,Function.update_self,adv_val_other _ _ _ K hKO hKS,
      List.flatMap_cons,List.length_append,List.nil_append,List.length_cons,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end NearQuarticWires.StageTuple
