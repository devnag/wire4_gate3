import Proof.Quartic.StageCertificateControl.FramePayload

/-!
# The counted native-cache payload scan

Paper: complete tables in `lem:print`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (read_pre)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- The counted native table scan of `lem:print`,
paper/paper.tex, consumes one actual cache frame
for each remaining test counter value. -/
def copyPayloads (src dst : Fin (ns+1)) (OP SC K : Fin nr) : WMX ns nr :=
  .whr K (.seq (WMX.dec K) (copyPayload src dst OP SC))

/-- The complete cache-copy state of `lem:print`, paper/paper.tex, appends payload marks while separately advancing
past every actual outer delimiter. -/
def payloadsEnd (σ : WState ns nr) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (payloads : List (List Bool)) : WState ns nr :=
  ((Control.copySt σ src dst OP SC payloads.flatten.length (marks payloads.flatten)).seth src
    (σ.sh src+(payloads.flatMap frame).length)).setv K 0

/-- The counted whole-cache scan of `lem:print` and `prop:time`,
paper/paper.tex, copies all
actual framed payloads in order. It retains exact destination bytes,
uses only read-bit equality on the source, and charges every delimiter. -/
theorem copyPayloads_exec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC) :
    ∀ (payloads : List (List Bool)) (rest : List Bool) (σ : WState ns nr),
      (∀ q,readTapeBit (σ.st src) (σ.sh src+q)=readTapeBit (payloads.flatMap frame++rest) q) →
      σ.sh dst=(σ.st dst).length → σ.val K=payloads.length → payloads.length≤cap →
      σ.val OP+4*payloads.flatten.length+4≤cap →
      σ.val SC+2*payloads.flatten.length+2≤cap →
    WXExec cap (copyPayloads src dst OP SC K) σ (payloadsEnd σ src dst OP SC K payloads)
      (100*(payloads.flatten.length+payloads.length+1))
  | [],rest,σ,_,hd,hK,_,_,_ => by
    have he : payloadsEnd σ src dst OP SC K []=σ := by
      apply WState.eq
      · funext i
        by_cases hi : i=src
        · subst i
          simp [payloadsEnd,Control.copySt,hsd]
        · by_cases hi' : i=dst
          · subst i
            simp [payloadsEnd,Control.copySt,hi,marks]
          · simp [payloadsEnd,Control.copySt,hi,hi']
      · funext i
        by_cases hi : i=dst
        · subst i
          simp [payloadsEnd,Control.copySt,marks]
        · simp [payloadsEnd,Control.copySt,hi]
      · funext i
        by_cases hi : i=K
        · subst i
          simp [payloadsEnd,hK]
        · by_cases ho : i=OP
          · subst i
            simp [payloadsEnd,Control.copySt,hi,hOS,marks]
          · by_cases hs : i=SC
            · subst i
              simp [payloadsEnd,Control.copySt,hi,ho]
            · simp [payloadsEnd,Control.copySt,hi,ho,hs]
      · rfl
    rw [he]
    exact (WXExec.whrF (by simpa using hK)).mono (by simp)
  | payload::payloads,rest,σ,hread,hd,hK,hlen,hcap,hscan => by
    have ed := WXExec.dec cap K σ (by rw [hK];exact hlen)
    let σ1 := σ.setv K payloads.length
    have ed' : WXExec cap (WMX.dec K) σ σ1 1 := by simpa only [hK,List.length_cons,Nat.add_sub_cancel] using ed
    have ec := copyPayload_exec cap σ1 src dst OP SC hsd hOS payload
      (payloads.flatMap frame++rest)
      (by intro q;simpa only [σ1,WState.setv_st,WState.setv_sh,List.flatMap_cons,List.append_assoc] using hread q)
      (by simpa only [σ1,WState.setv_sh,WState.setv_st] using hd)
      (by simp only [σ1,WState.setv_val,Function.update_of_ne (Ne.symm hKO)];
          simp only [List.flatten_cons,List.length_append] at hcap;omega)
      (by simp only [σ1,WState.setv_val,Function.update_of_ne (Ne.symm hKS)];
          simp only [List.flatten_cons,List.length_append] at hscan;omega)
    let σ2 := (Control.copySt σ1 src dst OP SC payload.length (marks payload)).seth src
      (σ1.sh src+2*payload.length+1)
    have hflat : payloads.flatten.length=(payloads.map List.length).sum := by simp
    have hnext : ∀ q,readTapeBit (σ2.st src) (σ2.sh src+q)=
        readTapeBit (payloads.flatMap frame++rest) q := by
      intro q
      have hh := hread ((frame payload).length+q)
      rw [List.flatMap_cons,List.append_assoc,read_pre] at hh
      simpa [σ2,σ1,Control.copySt,hsd,frame_length,Nat.add_assoc] using hh
    have ehd : σ2.sh dst=(σ2.st dst).length := by
      simp [σ2,σ1,Control.copySt,hsd.symm,hd,marks_length]
    have ehK : σ2.val K=payloads.length := by
      simp [σ2,σ1,Control.copySt,hKO,hKS]
    have ehcap : σ2.val OP+4*payloads.flatten.length+4≤cap := by
      simp [σ2,σ1,Control.copySt,hOS,Ne.symm hKO,marks_length]
      simp only [List.flatten_cons,List.length_append] at hcap
      omega
    have ehscan : σ2.val SC+2*payloads.flatten.length+2≤cap := by
      simp [σ2,σ1,Control.copySt,Ne.symm hKS]
      simp only [List.flatten_cons,List.length_append] at hscan
      omega
    have er := copyPayloads_exec cap src dst OP SC K hsd hOS hKO hKS payloads rest σ2 hnext ehd ehK
      (by simp only [List.length_cons] at hlen;omega) ehcap ehscan
    have hne : σ.val K≠0 := by rw [hK];simp
    refine (WXExec.whrT hne (WXExec.seq ed' ec) er).cast cap ?_ ?_
    · apply WState.eq
      · funext i
        by_cases hi : i=src
        · subst i
          simp [payloadsEnd,σ2,σ1,Control.copySt,hsd,frame_length,List.length_append]
          omega
        · by_cases ho : i=dst
          · subst i
            simp [payloadsEnd,σ2,σ1,Control.copySt,hi,marks_length,List.length_append]
            omega
          · simp [payloadsEnd,σ2,σ1,Control.copySt,hi,ho]
      · funext i
        by_cases hi : i=dst
        · subst i
          simp [payloadsEnd,σ2,σ1,Control.copySt,NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
        · simp [payloadsEnd,σ2,σ1,Control.copySt,hi]
      · funext i
        by_cases hi : i=K
        · subst i
          simp [payloadsEnd]
        · by_cases ho : i=OP
          · subst i
            simp [payloadsEnd,σ2,σ1,Control.copySt,hi,hOS,marks_length,List.length_append]
            omega
          · by_cases hs : i=SC
            · subst i
              simp [payloadsEnd,σ2,σ1,Control.copySt,hi,ho,List.length_append]
              omega
            · simp [payloadsEnd,σ2,σ1,Control.copySt,hi,ho,hs]
      · rfl
    · simp only [List.flatten_cons,List.length_append,List.length_cons]
      omega

end NearQuarticWires.StageCertificateControl
