import Proof.Quartic.StageCertificateControl.IndexedLoad

/-!
# Actual binary schedule selection after the cold scheduler call

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageCertTests

/-- `prop:time`, paper/paper.tex: the
copied scheduler frame is opened by its actual counter, and the actual
index selects the original binary five-field record. -/
def indexedSelectProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (.wm (openCopiedFrame (indexedExternal p 1) (indexedExternal p 2) indexedScheduleRegs))
    (.seq (.wm (WM.rewind (indexedExternal p 2) 15))
      (selectMetadata (indexedExternal p 2) (indexedExternal p 3) (indexedExternal p 4)
        indexedSelectionRegs))

/-- `prop:time`, paper/paper.tex: the
physical unframing, raw-source return, and record selection have their
exact state transitions, with no decoded record supplied as input. -/
noncomputable def indexedSelectedState {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2)
    (σ : WState (p.tapeCount+11) 32) : WState (p.tapeCount+11) 32 :=
  let a := (appendO (σ.setv 10 (2*r.prepared.output.length)) (indexedExternal p 2) 15
    r.prepared.output).seth (indexedExternal p 1) (2*r.prepared.output.length)
  let b := (a.setv 15 0).seth (indexedExternal p 2) 0
  selectedMetadataEnd b (indexedExternal p 2) (indexedExternal p 3) (indexedExternal p 4)
    indexedSelectionRegs
    ((certificateMetadata r.prepared.selected.1 r.prepared.call.kind).take r.index.val) r.metadata

/-- `prop:time`, paper/paper.tex: a
polynomial scalar source clock pays every copied scheduler byte and
every visited whole-test record. -/
noncomputable def indexedSelectCost {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  50000*(r.prepared.output.length+
    (certificateMetadata r.prepared.selected.1 r.prepared.call.kind).length+1)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the actual scheduler-frame bytes and actual
index determine the selected record by physical instructions alone.
Every arbitrary threshold is traversed in its binary encoding. -/
theorem indexedSelect_exec {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) (cap : ℕ)
    (σ : WState (p.tapeCount+11) 32)
    (hs : σ.st (indexedExternal p 1)=frame r.prepared.output)
    (hsh : σ.sh (indexedExternal p 1)=(frame r.prepared.output).length)
    (hr : σ.st (indexedExternal p 2)=[]) (hrh : σ.sh (indexedExternal p 2)=0)
    (hd : σ.sh (indexedExternal p 3)=(σ.st (indexedExternal p 3)).length)
    (hm : σ.st (indexedExternal p 4)=[]) (hmh : σ.sh (indexedExternal p 4)=0)
    (hOP : σ.val 10=(frame r.prepared.output).length) (hindex : σ.val 4=r.index.val)
    (hz : ∀ i∈([0,1,2,6,7,8,9,11,12,13,14,15] : List (Fin 32)),σ.val i=0)
    (hcap : 100*(r.prepared.output.length+r.index.val+1)≤cap) :
    WXExec cap (indexedSelectProgram p) σ (indexedSelectedState p r σ) (indexedSelectCost r) := by
  have ex {i j : Fin 11} (h : i≠j) : indexedExternal p i≠indexedExternal p j := by
    intro he
    apply h
    apply Fin.ext
    exact congrArg (fun x : Fin (p.tapeCount+12) => x.val) he
  have eo := openCopiedFrame_spec cap (indexedExternal p 1) (indexedExternal p 2)
    (ex (by decide)) indexedScheduleRegs r.prepared.output σ hs hsh
    (by rw [hr,hrh];rfl) hOP (hz 11 (by simp)) (hz 12 (by simp))
    (hz 13 (by simp)) (hz 14 (by simp))
    (by simp [Codec.frame_eq_marks] at hOP ⊢;omega)
    (by simp [indexedScheduleRegs,hz 15 (by simp)];omega)
  let a := (appendO (σ.setv 10 (2*r.prepared.output.length)) (indexedExternal p 2) 15
    r.prepared.output).seth (indexedExternal p 1) (2*r.prepared.output.length)
  have er := wrewind_spec cap (indexedExternal p 2) (15 : Fin 32) r.prepared.output.length a
    (by simp [a,appendO,hz 15 (by simp)])
    (by simp [a,appendO,hz 15 (by simp)];omega)
  let b := (a.setv 15 0).seth (indexedExternal p 2) 0
  have he : (a.setv 15 0).seth (indexedExternal p 2)
      (a.sh (indexedExternal p 2)-r.prepared.output.length)=b := by
    simp [b,a,appendO,ex (show (2 : Fin 11)≠1 by decide),hrh]
  rw [he] at er
  let ms := certificateMetadata r.prepared.selected.1 r.prepared.call.kind
  let skipped := ms.take r.index.val
  have htake : skipped.length=r.index.val := by
    have hj : r.index.val ≤ ms.length := r.index.isLt.le
    change (ms.take r.index.val).length=r.index.val
    rw [List.length_take,Nat.min_eq_left hj]
  have hsplit : r.prepared.output=skipped.flatMap TestMetadata.word++r.metadata.word++
      (ms.drop (r.index.val+1)).flatMap TestMetadata.word := by
    have h := metadataSelected_word ms r.index
    simpa only [metadataScalarFields_word,metadataFields_word,PreparedScheduleRequest.output,
      IndexedRequest.metadata,ms,skipped] using h
  have hlen : (skipped.flatMap TestMetadata.word).length+r.metadata.word.length≤r.prepared.output.length := by
    rw [hsplit,List.length_append,List.length_append]
    omega
  have hb6 : b.val (6 : Fin 32)=0 := by simp [b,a,appendO,hz 6 (by simp)]
  have es := selectMetadata_spec cap (indexedExternal p 2) (indexedExternal p 3) (indexedExternal p 4)
    indexedSelectionRegs (ex (by decide)) (ex (by decide)) (ex (by decide)) skipped r.metadata []
    ((ms.drop (r.index.val+1)).flatMap TestMetadata.word) b
    (by simpa [b,a,appendO,hr,List.append_assoc] using hsplit)
    (by simp [b])
    (by simp [b,a,appendO,ex (show (3 : Fin 11)≠2 by decide),
      ex (show (3 : Fin 11)≠1 by decide),hd])
    (by simp [b,a,appendO,ex (show (4 : Fin 11)≠2 by decide),hm])
    (by simp [b,a,appendO,ex (show (4 : Fin 11)≠2 by decide),
      ex (show (4 : Fin 11)≠1 by decide),hmh])
    (by intro i;fin_cases i <;> simp [b,a,appendO,indexedSelectionRegs,hz])
    (by simp [b,a,appendO,indexedSelectionRegs,hz])
    (by simp [b,a,appendO,indexedSelectionRegs,hz])
    (by simp [b,a,appendO,indexedSelectionRegs,hz])
    (by simp [b,a,appendO,indexedSelectionRegs,hindex,htake])
    (by omega) (by omega)
    (by
      change b.val (6 : Fin 32)+2*((skipped.flatMap TestMetadata.word).length+r.metadata.word.length)+10≤cap
      rw [hb6]
      omega)
  refine (WXExec.seq (WXExec.wm eo) ((WXExec.wm er).seq es)).cast cap rfl ?_
  unfold indexedSelectCost
  have hi := r.index.isLt
  change r.index.val < ms.length at hi
  rw [htake]
  omega

end NearQuarticWires.StageCertificateControl
