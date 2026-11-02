import Proof.Quartic.StageCertificateControl.IndexedSelect

/-!
# The actual retained binary threshold header

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
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageCertTests (TestMetadata)

/-- `prop:time`, paper/paper.tex: the
threshold header is produced from actual metadata bytes, and the saved
metadata head returns to zero for the unchanged base request. -/
def indexedThresholdState (p : Program) (m : TestMetadata) (σ : WState (p.tapeCount+11) 32) :
    WState (p.tapeCount+11) 32 :=
  let a := (appendO σ (indexedExternal p 5) 16 m.word).seth (indexedExternal p 4) (2*m.word.length)
  let b := (a.setv 16 0).seth (indexedExternal p 5) 0
  let c := b.setv 11 (2*m.word.length)
  let d := (c.setv 11 0).seth (indexedExternal p 4) 0
  let e := thresholdFieldsEnd d (indexedExternal p 5) (indexedExternal p 3) (indexedExternal p 6)
    indexedThresholdRegs m
  (e.sets (indexedExternal p 6) (frame (RepairRepresentation.natWord m.threshold))).seth (indexedExternal p 6) 0

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: binary threshold extraction,
including every measured return, has a clock linear in metadata bytes. -/
theorem indexedThreshold_exec (p : Program) (m : TestMetadata) (cap : ℕ)
    (σ : WState (p.tapeCount+11) 32)
    (hs : σ.st (indexedExternal p 4)=frame m.word) (hsh : σ.sh (indexedExternal p 4)=0)
    (hr : σ.st (indexedExternal p 5)=[]) (hrh : σ.sh (indexedExternal p 5)=0)
    (hd : σ.sh (indexedExternal p 3)=(σ.st (indexedExternal p 3)).length)
    (ht : σ.st (indexedExternal p 6)=[]) (hth : σ.sh (indexedExternal p 6)=0)
    (hmeta : σ.val 7=2*m.word.length)
    (hz : ∀ i∈([0,1,2,8,9,11,12,13,14,16,17,18] : List (Fin 32)),σ.val i=0)
    (hcap : 100*(m.word.length+1)≤cap) :
    WXExec cap (indexedThresholdProgram p) σ (indexedThresholdState p m σ) (3000*(m.word.length+1)) := by
  have ex {i j : Fin 11} (h : i≠j) : indexedExternal p i≠indexedExternal p j := by
    intro he;apply h;apply Fin.ext
    exact congrArg (fun x : Fin (p.tapeCount+12) => x.val) he
  have hm : (RepairRepresentation.natWord m.threshold).length ≤ m.word.length := by
    have h := congrArg List.length (metadataThreshold_word m)
    simp only [List.length_append] at h
    omega
  have eu := measuredUnframe_spec cap (indexedExternal p 4) (indexedExternal p 5) (ex (by decide))
    indexedMetadataRegs m.word σ hs hsh (by rw [hr,hrh];rfl) hmeta
    (hz 11 (by simp)) (hz 12 (by simp)) (hz 13 (by simp)) (hz 14 (by simp))
    (by omega) (by simp [indexedMetadataRegs,hz 16 (by simp)];omega)
  let a := (appendO σ (indexedExternal p 5) 16 m.word).seth (indexedExternal p 4) (2*m.word.length)
  have er := wrewind_spec cap (indexedExternal p 5) (16 : Fin 32) m.word.length a
    (by simp [a,appendO,hz 16 (by simp)])
    (by simp [a,appendO,hz 16 (by simp)];omega)
  let b := (a.setv 16 0).seth (indexedExternal p 5) 0
  have heb : (a.setv 16 0).seth (indexedExternal p 5) (a.sh (indexedExternal p 5)-m.word.length)=b := by
    simp [b,a,appendO,ex (show (5 : Fin 11)≠4 by decide),hrh]
  rw [heb] at er
  have ec := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (7 : Fin 32) 11 12 (by decide) (by decide) (by decide) b
    (by simp [b,a,appendO,hz]) (by simp [b,a,appendO,hz])
    (by simp [b,a,appendO,hmeta];omega)
  have hb7 : b.val (7 : Fin 32)=2*m.word.length := by simp [b,a,appendO,hmeta]
  rw [hb7] at ec
  let c := b.setv 11 (2*m.word.length)
  have ev := wrewind_spec cap (indexedExternal p 4) (11 : Fin 32) (2*m.word.length) c
    (by simp [c]) (by simp [c];omega)
  let d := (c.setv 11 0).seth (indexedExternal p 4) 0
  have hed : (c.setv 11 0).seth (indexedExternal p 4) (c.sh (indexedExternal p 4)-2*m.word.length)=d := by
    simp [d,c,b,a,ex (show (4 : Fin 11)≠5 by decide)]
  rw [hed] at ev
  have et := copyThresholdFields_spec cap (indexedExternal p 5) (indexedExternal p 3) (indexedExternal p 6)
    indexedThresholdRegs (ex (by decide)) (ex (by decide)) (ex (by decide)) m [] [] d
    (by simp [d,c,b,a,appendO,hr])
    (by simp [d,c,b,ex (show (5 : Fin 11)≠4 by decide)])
    (by simp [d,c,b,a,appendO,ex (show (3 : Fin 11)≠4 by decide),
      ex (show (3 : Fin 11)≠5 by decide),hd])
    (by simp [d,c,b,a,appendO,ex (show (6 : Fin 11)≠4 by decide),
      ex (show (6 : Fin 11)≠5 by decide),hth,ht])
    (by intro i;fin_cases i <;> simp [d,c,b,a,appendO,indexedThresholdRegs,hz])
    (by omega)
    (by simp [d,c,b,a,appendO,indexedThresholdRegs,hz];omega)
    (by simp [d,c,b,a,appendO,indexedThresholdRegs,hz];omega)
  let e := thresholdFieldsEnd d (indexedExternal p 5) (indexedExternal p 3) (indexedExternal p 6)
    indexedThresholdRegs m
  have ef := finishMarkedCopy_spec cap (indexedExternal p 6) (18 : Fin 32) 8 9
    (by decide) (by decide) (by decide) (RepairRepresentation.natWord m.threshold) e
    (by
      rw [thresholdFieldsEnd_value d _ _ _ _ _ (ex (by decide))]
      simp [d,c,b,a,appendO,ex (show (6 : Fin 11)≠5 by decide),ht])
    (by simp [e,thresholdFieldsEnd,fixedFieldsEnd,appendO,rawFieldsWord,indexedThresholdRegs,
      d,c,b,a,ex (show (6 : Fin 11)≠3 by decide),ex (show (6 : Fin 11)≠5 by decide),
      ex (show (6 : Fin 11)≠4 by decide),hth,marks_length])
    (by simp [e,thresholdFieldsEnd,fixedFieldsEnd,appendO,rawFieldsWord,indexedThresholdRegs,
      d,c,b,a,hz,marks_length])
    (by simp [e,thresholdFieldsEnd,fixedFieldsEnd,appendO,indexedThresholdRegs,d,c,b,a,hz])
    (by simp [e,thresholdFieldsEnd,fixedFieldsEnd,appendO,indexedThresholdRegs,d,c,b,a,hz])
    (by omega)
  refine (WXExec.seq (WXExec.wm eu) ((WXExec.wm er).seq ((WXExec.wm ec).seq
    ((WXExec.wm ev).seq (et.seq (WXExec.wm ef)))))).mono ?_
  omega

end NearQuarticWires.StageCertificateControl
