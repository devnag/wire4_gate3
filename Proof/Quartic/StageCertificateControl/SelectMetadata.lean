import Proof.Quartic.StageCertificateControl.ThresholdFields
import Proof.Quartic.StageCertificateControl.FinishMarked

/-!
# Select a whole-test metadata record from the actual scheduler output

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
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageCertTests (TestMetadata)

variable {ns nr : ℕ}

/-- `sec:algorithm`, paper/paper.tex: the actual
index skips whole records, copies exactly five fields, closes their
frame, and returns the saved metadata tape by measured instructions. -/
def selectMetadata (src discard saved : Fin (ns+1)) (R : Fin 8 ↪ Fin nr) : WMX ns nr :=
  .seq (copyMetadataPrefix src discard (R 0) (R 1) (R 3) (R 2) (R 5))
    (.seq (copyMetadataRecord src saved (R 0) (R 1) (R 4) (R 2))
      (.wm (finishMarkedCopy saved (R 4) (R 6) (R 7))))

/-- `prop:time`, paper/paper.tex: the exact
selected metadata frame is retained separately from the skipped stream;
its measured count is kept for the scheduler-output head return. -/
def selectedMetadataEnd (σ : WState ns nr) (src discard saved : Fin (ns+1))
    (R : Fin 8 ↪ Fin nr) (skipped : List TestMetadata) (m : TestMetadata) : WState ns nr :=
  let a := metadataPrefixEnd σ src discard (R 3) (R 5) skipped
  let b := metadataRecordEnd a src saved (R 4) m
  (b.sets saved (frame m.word)).seth saved 0

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: selecting the actual record uses only its
index and binary bytes. The potentially enormous threshold is copied
without ever becoming a unary register value. -/
theorem selectMetadata_spec (cap : ℕ) (src discard saved : Fin (ns+1))
    (R : Fin 8 ↪ Fin nr) (hsd : src≠discard) (hsv : src≠saved) (hds : discard≠saved)
    (skipped : List TestMetadata) (m : TestMetadata) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src=pre++skipped.flatMap TestMetadata.word++m.word++rest)
    (hsh : σ.sh src=pre.length) (hd : σ.sh discard=(σ.st discard).length)
    (hs : σ.st saved=[]) (hhead : σ.sh saved=0)
    (hz : ∀ i : Fin 3,σ.val (R i.castSucc.castSucc.castSucc.castSucc.castSucc)=0)
    (h4 : σ.val (R 4)=0) (h6 : σ.val (R 6)=0) (h7 : σ.val (R 7)=0)
    (hindex : σ.val (R 5)=skipped.length) (hcount : skipped.length≤cap) (hfive : 5≤cap)
    (hcap : σ.val (R 3)+2*((skipped.flatMap TestMetadata.word).length+m.word.length)+10≤cap) :
    WXExec cap (selectMetadata src discard saved R) σ
      (selectedMetadataEnd σ src discard saved R skipped m)
      (20000*((skipped.flatMap TestMetadata.word).length+m.word.length+skipped.length+1)) := by
  have rn {i j : Fin 8} (h : i≠j) : R i≠R j := R.injective.ne h
  have h0 : σ.val (R 0)=0 := hz 0
  have h1 : σ.val (R 1)=0 := hz 1
  have h2 : σ.val (R 2)=0 := hz 2
  have ep := copyMetadataPrefix_spec cap src discard (R 0) (R 1) (R 3) (R 2) (R 5)
    hsd (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide)) (rn (by decide))
    skipped pre (m.word++rest) σ (by simpa only [List.append_assoc] using hst)
    hsh hd h0 h1 h2 hindex hcount hfive (by omega)
  let a := metadataPrefixEnd σ src discard (R 3) (R 5) skipped
  have em := copyMetadataRecord_spec cap src saved (R 0) (R 1) (R 4) (R 2)
    hsv (rn (by decide)) (rn (by decide)) (rn (by decide))
    (rn (by decide)) (rn (by decide)) (rn (by decide)) m
    (pre++skipped.flatMap TestMetadata.word) rest a
    (by simpa [a,metadataPrefixEnd,appendO,hsd,List.append_assoc] using hst)
    (by simp [a,metadataPrefixEnd,appendO,hsh])
    (by simp [a,metadataPrefixEnd,appendO,hds.symm,hsv.symm,hs,hhead])
    (by simp [a,metadataPrefixEnd,appendO,rn (show (0 : Fin 8)≠5 by decide),
      rn (show (0 : Fin 8)≠3 by decide),h0])
    (by simp [a,metadataPrefixEnd,appendO,rn (show (1 : Fin 8)≠5 by decide),
      rn (show (1 : Fin 8)≠3 by decide),h1])
    (by simp [a,metadataPrefixEnd,appendO,rn (show (2 : Fin 8)≠5 by decide),
      rn (show (2 : Fin 8)≠3 by decide),h2]) hfive
    (by simp [a,metadataPrefixEnd,appendO,rn (show (4 : Fin 8)≠5 by decide),
      rn (show (4 : Fin 8)≠3 by decide),h4];omega)
  let b := metadataRecordEnd a src saved (R 4) m
  have ef := finishMarkedCopy_spec cap saved (R 4) (R 6) (R 7)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) m.word b
    (by simp [b,metadataRecordEnd,a,metadataPrefixEnd,appendO,hds.symm,hs])
    (by simp [b,metadataRecordEnd,a,metadataPrefixEnd,appendO,hsv.symm,hds.symm,
      hhead,marks_length])
    (by simp [b,metadataRecordEnd,a,metadataPrefixEnd,appendO,rn (show (4 : Fin 8)≠5 by decide),
      rn (show (4 : Fin 8)≠3 by decide),h4,marks_length])
    (by simp [b,metadataRecordEnd,a,metadataPrefixEnd,appendO,rn (show (6 : Fin 8)≠4 by decide),
      rn (show (6 : Fin 8)≠5 by decide),rn (show (6 : Fin 8)≠3 by decide),h6])
    (by simp [b,metadataRecordEnd,a,metadataPrefixEnd,appendO,rn (show (7 : Fin 8)≠4 by decide),
      rn (show (7 : Fin 8)≠5 by decide),rn (show (7 : Fin 8)≠3 by decide),h7])
    (by omega)
  exact (ep.seq (em.seq (WXExec.wm ef))).mono (by omega)

/-- `sec:algorithm`, paper/paper.tex: the retained
record is the exact original five-field frame with its head at zero. -/
theorem selectedMetadataEnd_saved (σ : WState ns nr) (src discard saved : Fin (ns+1))
    (R : Fin 8 ↪ Fin nr) (skipped : List TestMetadata) (m : TestMetadata) :
    (selectedMetadataEnd σ src discard saved R skipped m).st saved=frame m.word ∧
      (selectedMetadataEnd σ src discard saved R skipped m).sh saved=0 := by
  simp [selectedMetadataEnd]

/-- `prop:time`, paper/paper.tex: the
scheduler head is left at exactly the bytes that were copied; the two
actual counters retain twice the skipped and selected-record lengths. -/
theorem selectedMetadataEnd_measurements (σ : WState ns nr) (src discard saved : Fin (ns+1))
    (R : Fin 8 ↪ Fin nr) (skipped : List TestMetadata) (m : TestMetadata)
    (hsv : src≠saved) (h4 : σ.val (R 4)=0) :
    (selectedMetadataEnd σ src discard saved R skipped m).sh src=
      σ.sh src+(skipped.flatMap TestMetadata.word).length+m.word.length ∧
    (selectedMetadataEnd σ src discard saved R skipped m).val (R 3)=
      σ.val (R 3)+2*(skipped.flatMap TestMetadata.word).length ∧
    (selectedMetadataEnd σ src discard saved R skipped m).val (R 4)=2*m.word.length := by
  have rn {i j : Fin 8} (h : i≠j) : R i≠R j := R.injective.ne h
  simp [selectedMetadataEnd,metadataRecordEnd,metadataPrefixEnd,appendO,hsv,marks_length,
    rn (show (3 : Fin 8)≠4 by decide),rn (show (3 : Fin 8)≠5 by decide),
    rn (show (4 : Fin 8)≠5 by decide),rn (show (4 : Fin 8)≠3 by decide),h4]

end NearQuarticWires.StageCertificateControl
