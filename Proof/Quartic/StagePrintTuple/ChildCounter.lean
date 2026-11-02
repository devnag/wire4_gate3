import Proof.Quartic.StagePrintTuple.FrameCount
import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: a finite
original compiler record stream is the entire counter input; its child
count is not a runtime field or a separate source premise. -/
structure ChildCountRequest where
  records : List (List Bool)
  nonempty : ∀ record∈records,record≠[]

/-- `lem:print`, paper/paper.tex: actual
compiler records are concatenated in their unchanged original order. -/
def ChildCountRequest.word (r : ChildCountRequest) : List Bool := r.records.flatMap frame

/-- `lem:print`, paper/paper.tex: the physical
counter emits its computed count in the ordinary natural codec. -/
def ChildCountRequest.output (r : ChildCountRequest) : List Bool := frame (natWord r.records.length)

/-- `lem:print`, paper/paper.tex: count writing
uses eight distinct registers separate from the raw frame scan counter. -/
def childCountWriter : Fin 8 ↪ Fin 11 := ⟨![0,1,2,3,4,5,6,7],by decide⟩

/-- `lem:print`, paper/paper.tex: the cold
counter unframes the actual record source, scans its real child frames,
then prints the computed count and its complete output frame. -/
def childCountProgram : WM 2 11 :=
  .seq (StageGamma.unframeRecord 0 1 8)
    (.seq (countChildFrames 1 10 0)
      (.seq (writeNatM 2 childCountWriter) (emitC 2 7 false)))

/-- `prop:time`, paper/paper.tex: the counter's
ordinary capacity covers actual source bits and its computed count. -/
def ChildCountRequest.capacity (r : ChildCountRequest) : ℕ :=
  100*(r.word.length+r.records.length+10)

/-- `prop:time`, paper/paper.tex: every source
scan, marker step and count-codec write is charged explicitly. -/
def ChildCountRequest.steps (r : ChildCountRequest) : ℕ :=
  100*r.word.length+20*r.records.length+
    (natBitLength r.records.length+10)*(100*r.records.length+200)+100

/-- `prop:time`, paper/paper.tex: the binary
length of a physically computed finite count is at most its value plus1. -/
theorem childCount_bits (j : ℕ) : natBitLength j≤j+1 := by
  unfold natBitLength
  have h1:=Nat.log_lt_self 2 (show j+1≠0 by omega)
  have h2:=Nat.log_mono_right (show j≤j+1 by omega) (b:=2)
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold counter computes and writes the exact
number of ORIGINAL child records, including an empty record stream. -/
theorem childCountProgram_spec (r : ChildCountRequest) :
    ∃ τ, WExec r.capacity childCountProgram
      (idealStart 2 11 r.word (fun _=>0)) τ r.steps ∧ τ.st 2=r.output := by
  let σ := idealStart 2 11 r.word (fun _=>0)
  have e1 := StageGamma.unframeRecord_run r.capacity (0 : Fin 3) 1 (by decide) (8 : Fin 11)
    r.word [] [] σ (by simp [σ,idealStart]) rfl rfl rfl (by unfold ChildCountRequest.capacity;omega)
  let s1 := (σ.sets 1 r.word).seth 0 (2*r.word.length+1)
  have e1' : WExec r.capacity (StageGamma.unframeRecord 0 1 8) σ s1 (23*r.word.length+5) := by
    simpa [s1,σ,idealStart] using e1
  have e2 := countChildFrames_spec r.capacity (1 : Fin 3) 2 (7 : Fin 11) 10 0
    (by decide) (by decide) (by decide) (by decide) [] (by rfl) r.records [] s1 r.nonempty
    (by simp [s1,σ,idealStart,ChildCountRequest.word])
    (by simp [s1,σ,idealStart]) (by simp [s1,σ,idealStart])
    (by simp [s1,σ,idealStart]) (by
      change 0+(r.records.flatMap frame).length≤r.capacity
      simpa only [ChildCountRequest.word,Nat.zero_add] using (show r.word.length≤r.capacity by
        unfold ChildCountRequest.capacity
        omega))
    (by simp [s1,σ,idealStart];unfold ChildCountRequest.capacity;omega)
  let s2 := (adv (1 : Fin 3) 2 (7 : Fin 11) 10 s1 [] r.word.length).setv 0 r.records.length
  have e2' : WExec r.capacity (countChildFrames 1 10 0) s1 s2
      (40*r.word.length+10*r.records.length+1) := by
    simpa [s2,ChildCountRequest.word,s1,σ,idealStart] using e2
  have hbits := childCount_bits r.records.length
  have e3 := writeNatM_spec r.capacity (2 : Fin 3) childCountWriter s2
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp [s2,s1,σ,idealStart,adv,appendO,childCountWriter])
    (by simp only [s2,WState.setv_val,childCountWriter,Fin.isValue,Fin.reduceFinMk,
        Function.Embedding.coeFn_mk,Matrix.cons_val_zero,Function.update_self]
        simp [s1,σ,idealStart,adv,appendO,childCountWriter]
        unfold ChildCountRequest.capacity
        omega)
  let s3 := appendO s2 (2 : Fin 3) (7 : Fin 11)
    (Streaming.marks (natWord r.records.length))
  have e3' : WExec r.capacity (writeNatM 2 childCountWriter) s2 s3
      ((natBitLength r.records.length+10)*(100*r.records.length+200)) := by
    simpa [s2,childCountWriter] using e3
  have e4 := Codec.emitBit_spec r.capacity (2 : Fin 3) (7 : Fin 11) false s3
    (by simp [s3,s2,s1,σ,idealStart,adv,appendO])
    (by simp [s3,s2,s1,σ,idealStart,adv,appendO,Codec.marks_length]
        unfold ChildCountRequest.capacity
        omega)
  refine ⟨appendO s3 (2 : Fin 3) 7 [false],
    (e1'.seq (e2'.seq (e3'.seq e4))).mono (by unfold ChildCountRequest.steps;omega),?_⟩
  simp [s3,s2,s1,σ,idealStart,adv,appendO,ChildCountRequest.output,Codec.frame_eq_marks]

/-- `lem:print`, paper/paper.tex: the genuine
ordinary child-counter word function starts only from the actual raw
compiler records and prints its computed count, with complete return
and tape framing costs included. -/
noncomputable def childCounterWordFunction :
    WordFunction ChildCountRequest ChildCountRequest.word ChildCountRequest.output
      (fun r=>2*r.steps+2) :=
  wordFunction_of_ideal (.wm childCountProgram) (2 : Fin 3) (by decide)
    ChildCountRequest.capacity (fun _ _=>0) ChildCountRequest.steps (fun _=>le_rfl)
    (by
      intro r
      obtain ⟨τ,he,ho⟩ := childCountProgram_spec r
      exact ⟨rfl,τ,WXExec.wm he,ho⟩)

end NearQuarticWires.StageTuple
