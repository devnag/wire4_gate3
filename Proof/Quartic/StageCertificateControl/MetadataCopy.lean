import Proof.Quartic.StageCertificateControl.MetadataFields
import Proof.Quartic.StageCertificateControl.RawReturn
import Proof.Quartic.Control.Request

/-!
# Actual five-field metadata copies

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
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

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: a whole metadata record initializes its own
literal five-field counter and copies only actual encoded bits. -/
def copyMetadataRecord (src dst : Fin (ns+1)) (f c OP K : Fin nr) : WMX ns nr :=
  .seq (Control.incTimes K 5) (.wm (copyRawFields src dst f c OP K))

/-- `sec:algorithm`, paper/paper.tex: one whole
metadata copy appends every original field and advances by the exact
raw scheduler bytes, retaining the original scalar registers. -/
def metadataRecordEnd (σ : WState ns nr) (src dst : Fin (ns+1)) (OP : Fin nr)
    (m : TestMetadata) : WState ns nr :=
  (appendO σ dst OP (marks m.word)).seth src (σ.sh src+m.word.length)

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: copying a complete metadata record
costs its binary length, with no numeric decoding of its threshold. -/
theorem copyMetadataRecord_spec (cap : ℕ) (src dst : Fin (ns+1)) (f c OP K : Fin nr)
    (hsd : src≠dst) (hfc : f≠c) (hfO : f≠OP) (hcO : c≠OP)
    (hKf : K≠f) (hKc : K≠c) (hKO : K≠OP)
    (m : TestMetadata) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src=pre++m.word++rest) (hsh : σ.sh src=pre.length)
    (hd : σ.sh dst=(σ.st dst).length) (hf : σ.val f=0) (hc : σ.val c=0) (hK : σ.val K=0)
    (hfive : 5≤cap) (hcap : σ.val OP+2*m.word.length+2≤cap) :
    WXExec cap (copyMetadataRecord src dst f c OP K) σ (metadataRecordEnd σ src dst OP m)
      (1000*(m.word.length+1)) := by
  have ei := Control.incTimes_exec cap K 5 σ (by rw [hK];exact hfive)
  rw [hK,Nat.zero_add] at ei
  let a := σ.setv K 5
  have er := copyRawFields_spec cap src dst f c OP K hsd hfc hfO hcO hKf hKc hKO
    (metadataFields m) pre rest a
    (by simpa only [a,WState.setv_st,metadataFields_word] using hst) hsh hd
    (by simp [a,Function.update_of_ne hKf.symm,hf])
    (by simp [a,Function.update_of_ne hKc.symm,hc])
    (by simp [a,metadataFields_length]) (by rw [metadataFields_length];exact hfive)
    (by simpa only [a,WState.setv_val,Function.update_of_ne hKO.symm,metadataFields_word] using hcap)
  have he : rawFieldsEnd a src dst OP K (metadataFields m)=metadataRecordEnd σ src dst OP m := by
    apply WState.eq
    · simp [rawFieldsEnd,metadataRecordEnd,metadataFields_word,appendO,a]
    · simp [rawFieldsEnd,metadataRecordEnd,metadataFields_word,appendO,a]
    · funext i
      by_cases hi : i=K
      · subst i;simp [rawFieldsEnd,metadataRecordEnd,appendO,hKO,hK]
      · by_cases ho : i=OP
        · subst i;simp [rawFieldsEnd,metadataRecordEnd,appendO,a,hKO.symm,hi,metadataFields_word]
        · simp [rawFieldsEnd,metadataRecordEnd,appendO,a,Function.update_of_ne hi,
            Function.update_of_ne ho,hKO.symm,metadataFields_word]
    · rfl
  refine (ei.seq (WXExec.wm er)).cast cap he ?_
  rw [metadataFields_length,metadataFields_word]
  omega

end NearQuarticWires.StageCertificateControl
