import Proof.Gates.Codec.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close

variable {ns nr : ℕ} (cap : ℕ)

/-- `lem:print`, paper/paper.tex: a counted stream is printed to an exact fresh frame from its actual read bits, including implicit trailing zero cells. -/
theorem frameStream_read (src dst : Fin (ns+1)) (hsd : src≠dst) (OP K : Fin nr) (hKO : K≠OP) :
    ∀ (Y : List Bool) (σ : WState ns nr),
      (∀k<Y.length,readTapeBit (σ.st src) (σ.sh src+k)=Y.getD k false)→
      σ.sh dst=(σ.st dst).length→σ.val K=Y.length→Y.length≤cap→σ.val OP+2*Y.length≤cap→
    WExec cap (Codec.frameStream src dst OP K) σ
      (((appendO σ dst OP (marks Y)).setv K 0).seth src (σ.sh src+Y.length)) (22*Y.length+1)
  | [],σ,_,hd,hK,_,_ => by
    have he : ((appendO σ dst OP (marks ([] : List Bool))).setv K 0).seth src (σ.sh src+0)=σ := by
      rw [show marks ([] : List Bool)=[] by rfl,appendO_nil σ dst OP]
      apply WState.eq
      · funext i
        by_cases hi : i=src
        · subst hi;simp
        · simp [Function.update_of_ne hi]
      · rfl
      · funext i
        by_cases hi : i=K
        · subst hi;simpa using hK.symm
        · simp [Function.update_of_ne hi]
      · rfl
    simp only [List.length_nil]
    rw [he]
    exact WExec.mono (WExec.whrF (by simpa using hK)) (by simp)
  | b::Y,σ,hread,hd,hK,hlen,hc => by
    have e1:=WExec.dec (cap:=cap) K σ (by rw [hK];simpa using hlen)
    let σ1:=σ.setv K (σ.val K-1)
    have hb : readTapeBit (σ1.st src) (σ1.sh src)=b := by
      have hh:=hread 0 (by simp)
      simpa [σ1] using hh
    have e2:=Codec.frameCell_spec cap src dst hsd OP σ1 (by simpa [σ1] using hd)
      (by simp only [σ1,WState.setv_val,Function.update_of_ne hKO.symm];simp only [List.length_cons] at hc;omega)
    rw [hb] at e2
    let σ2:=(appendO σ1 dst OP [true,b]).seth src (σ1.sh src+1)
    have htread : ∀k<Y.length,readTapeBit (σ2.st src) (σ2.sh src+k)=Y.getD k false := by
      intro k hk
      have hh:=hread (k+1) (by simp;omega)
      simpa [σ2,σ1,appendO,Function.update_of_ne hsd,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    have e3:=frameStream_read src dst hsd OP K hKO Y σ2 htread
      (by simp [σ2,σ1,appendO,Function.update_of_ne hsd.symm,hd])
      (by simp [σ2,σ1,appendO,Function.update_of_ne hKO,hK])
      (by simp only [List.length_cons] at hlen;omega)
      (by simp [σ2,σ1,appendO,Function.update_of_ne hKO.symm];simp only [List.length_cons] at hc;omega)
    have hne : σ.val K≠0 := by rw [hK];simp
    refine (WExec.whrT hne (WExec.seq e1 e2) e3).cast cap ?_ (by simp;omega)
    apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst hi;simp [σ2,σ1,appendO,hsd];omega
      · by_cases hid : i=dst
        · subst hid;simp [σ2,σ1,appendO,hi,hd,marks];ring
        · simp [σ2,σ1,appendO,hi,hid]
    · funext i
      by_cases hi : i=dst
      · subst hi;simp [σ2,σ1,appendO,hsd.symm,marks]
      · simp [σ2,σ1,appendO,hi]
    · funext i
      by_cases hi : i=K
      · subst hi;simp [σ2,σ1,appendO,hKO]
      · by_cases hio : i=OP
        · subst hio;simp [σ2,σ1,appendO,hi,marks];ring
        · simp [σ2,σ1,appendO,hi,hio]
    · rfl

end NearQuarticWires.StagePrint
