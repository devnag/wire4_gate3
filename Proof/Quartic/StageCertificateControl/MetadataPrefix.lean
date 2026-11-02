import Proof.Quartic.StageCertificateControl.MetadataCopy

/-!
# The actual skipped whole-test metadata prefix

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.WordPrograms
open StageCertTests (TestMetadata)

variable {ns nr : ℕ}

/-- `sec:algorithm`, paper/paper.tex: the actual
test index counts complete five-field records, not numeric thresholds. -/
def copyMetadataPrefix (src dst : Fin (ns+1)) (f c OP K I : Fin nr) : WMX ns nr :=
  .whr I (.seq (WMX.dec I) (copyMetadataRecord src dst f c OP K))

/-- `prop:time`, paper/paper.tex: all skipped
binary metadata is retained in a discard stream with its true marked
byte count, while the index counter is consumed exactly. -/
def metadataPrefixEnd (σ : WState ns nr) (src dst : Fin (ns+1)) (OP I : Fin nr)
    (ms : List TestMetadata) : WState ns nr :=
  ((appendO σ dst OP (marks (ms.flatMap TestMetadata.word))).seth src
    (σ.sh src+(ms.flatMap TestMetadata.word).length)).setv I 0

/-- `prop:time`, paper/paper.tex: the real
record-index loop traverses only actual metadata bits and restores its
inner five-field counter after every record. Its clock is linear in
encoded bytes and record count, with no threshold-magnitude factor. -/
theorem copyMetadataPrefix_spec (cap : ℕ) (src dst : Fin (ns+1)) (f c OP K I : Fin nr)
    (hsd : src≠dst) (hfc : f≠c) (hfO : f≠OP) (hcO : c≠OP)
    (hKf : K≠f) (hKc : K≠c) (hKO : K≠OP)
    (hIf : I≠f) (hIc : I≠c) (hIO : I≠OP) (hIK : I≠K) :
    ∀(ms : List TestMetadata) (pre rest : List Bool) (σ : WState ns nr),
      σ.st src=pre++ms.flatMap TestMetadata.word++rest→σ.sh src=pre.length→
      σ.sh dst=(σ.st dst).length→σ.val f=0→σ.val c=0→σ.val K=0→σ.val I=ms.length→
      ms.length≤cap→5≤cap→σ.val OP+2*(ms.flatMap TestMetadata.word).length+2≤cap→
      WXExec cap (copyMetadataPrefix src dst f c OP K I) σ (metadataPrefixEnd σ src dst OP I ms)
        (10000*((ms.flatMap TestMetadata.word).length+ms.length+1))
  | [],pre,rest,σ,_,_,_,_,_,_,hI,_,_,_ => by
    have he : metadataPrefixEnd σ src dst OP I []=σ := by
      simp only [metadataPrefixEnd,List.flatMap_nil,marks,List.length_nil,Nat.add_zero,appendO_nil]
      have hh : (σ.seth src (σ.sh src)).setv I 0=σ := by
        apply WState.eq
        · simp
        · rfl
        · funext i
          by_cases hi : i=I
          · subst i;simp [hI]
          · simp [Function.update_of_ne hi]
        · rfl
      exact hh
    rw [he]
    exact (WXExec.whrF (by simpa using hI)).mono (by simp)
  | m::ms,pre,rest,σ,hst,hsh,hd,hf,hc,hK,hI,hcount,hfive,hcap => by
    have hlen : ((m::ms).flatMap TestMetadata.word).length=m.word.length+
        (ms.flatMap TestMetadata.word).length := by simp
    have ed := WXExec.dec cap I σ (by rw [hI];exact hcount)
    let a := σ.setv I ms.length
    have ea : σ.setv I (σ.val I-1)=a := by rw [hI];rfl
    rw [ea] at ed
    have eb := copyMetadataRecord_spec cap src dst f c OP K hsd hfc hfO hcO hKf hKc hKO m pre
      (ms.flatMap TestMetadata.word++rest) a
      (by simpa only [a,WState.setv_st,List.flatMap_cons,List.append_assoc] using hst) hsh hd
      (by simp [a,Function.update_of_ne hIf.symm,hf])
      (by simp [a,Function.update_of_ne hIc.symm,hc])
      (by simp [a,Function.update_of_ne hIK.symm,hK]) hfive
      (by simp only [a,WState.setv_val,Function.update_of_ne hIO.symm];rw [hlen] at hcap;omega)
    let b := metadataRecordEnd a src dst OP m
    have hnext : b.st src=(pre++m.word)++ms.flatMap TestMetadata.word++rest := by
      simpa [b,metadataRecordEnd,appendO,hsd,a,List.append_assoc] using hst
    have hh : b.sh src=(pre++m.word).length := by simp [b,metadataRecordEnd,a,hsh]
    have hout : b.sh dst=(b.st dst).length := by simp [b,metadataRecordEnd,a,appendO,hsd.symm,hd]
    have hff : b.val f=0 := by simp [b,metadataRecordEnd,appendO,hfO,a,hIf.symm,hf]
    have hcc : b.val c=0 := by simp [b,metadataRecordEnd,appendO,hcO,a,hIc.symm,hc]
    have hKK : b.val K=0 := by simp [b,metadataRecordEnd,appendO,hKO,a,hIK.symm,hK]
    have hII : b.val I=ms.length := by simp [b,metadataRecordEnd,appendO,hIO,a]
    have htail : b.val OP+2*(ms.flatMap TestMetadata.word).length+2≤cap := by
      simp only [b,metadataRecordEnd,WState.seth_val,appendO,WState.setv_val,Function.update_self,
        a,Function.update_of_ne hIO.symm,marks_length]
      rw [hlen] at hcap
      omega
    have er := copyMetadataPrefix_spec cap src dst f c OP K I hsd hfc hfO hcO hKf hKc hKO hIf hIc hIO hIK
      ms (pre++m.word) rest b hnext hh hout hff hcc hKK hII
      (by simp only [List.length_cons] at hcount;omega) hfive htail
    refine (WXExec.whrT (by rw [hI];simp) (ed.seq eb) er).cast cap ?_ ?_
    · apply WState.eq
      · funext i
        by_cases hi : i=src
        · subst i;simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,hsd,hsh];omega
        · by_cases ho : i=dst
          · subst i;simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,hi,marks_length];omega
          · simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,hi,ho]
      · funext i
        by_cases hi : i=dst
        · subst i;simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,
            NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
        · simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,hi]
      · funext i
        by_cases hi : i=I
        · subst i;simp [metadataPrefixEnd]
        · by_cases ho : i=OP
          · subst i;simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,hi,marks_length];omega
          · simp [metadataPrefixEnd,b,metadataRecordEnd,a,appendO,hi,ho]
      · rfl
    · simp only [hlen,List.length_cons]
      omega

end NearQuarticWires.StageCertificateControl
