import Proof.Quartic.StageCertificateControl.BitmapWidths

/-!
# Literal signed native tables supplied to the bitmap consumer

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and `sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: the bitmap input consists of the actual original
preparation and its complete signed native test streams. The shape and
width conditions concern these physically supplied records, on every
witness, before any column has been certified. -/
structure BitmapRequest (B1 B2 coefficient degree : ℕ) where
  call : Call
  witness : List Bool
  tests : List NativeTest
  count_eq : tests.length=countHeaderValue B1 B2 call
  lengths : ∀p : Program.Selected call,Program.dispatch B1 B2 call=some p→
    ∀test∈tests,test.values.length=paddedCount call.n p.1.k
  values_fit : ∀test∈tests,∀z∈test.values,encS z<2^test.width
  widths : ∀test∈tests,test.width≤coefficient*(call.n+1)^degree
  threshold_bits : ∀p : Program.Selected call,Program.dispatch B1 B2 call=some p→
    ∀test∈tests,natBitLength test.bound≤StageCertTests.scheduleHint p.1

/-- `sec:algorithm`, paper/paper.tex: the native
consumer receives the original preparation, actual counted-test header,
and unchanged complete signed record streams in test-major order. -/
noncomputable def BitmapRequest.word {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) : List Bool :=
  Program.prepWord B1 B2 r.call r.witness++natWord r.tests.length++nativeTestStream r.tests

/-- `sec:params` and `sec:algorithm`, paper/paper.tex: a dispatched native input retains exactly its
original call, selected parameters and bounded witness prefix. -/
theorem BitmapRequest.word_selected {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) :
    r.word=true::(callWord r.call++Program.parametersWord p.1++
      frame (Program.witnessPrefix r.call p.1 r.witness)++natWord r.tests.length++
      nativeTestStream r.tests) := by
  unfold BitmapRequest.word Program.prepWord Program.stageWord
  rw [hd]
  simp only [List.cons_append,List.append_assoc]

/-- `sec:params`, paper/paper.tex: the default tag
precedes every following table byte and is handled without scanning it. -/
theorem BitmapRequest.word_default {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree)
    (hd : Program.dispatch B1 B2 r.call=none) :
    ∃rest,r.word=false::rest := by
  unfold BitmapRequest.word Program.prepWord Program.stageWord
  rw [hd]
  exact ⟨_,rfl⟩

/-- `sec:algorithm`, paper/paper.tex: the successful
native stream has exactly the public whole-test census used by the
physical scheduler and the count bootstrap. -/
theorem BitmapRequest.count_selected {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) :
    r.tests.length=(StageCertTests.certificateMetadata p.1 r.call.kind).length := by
  rw [r.count_eq,countHeaderValue,hd]

/-- `sec:algorithm`, paper/paper.tex: all signed
tables are conjoined over the full native census; only the final output
is cropped to the original center prefix. The default suffix is empty. -/
noncomputable def BitmapRequest.output {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) : List Bool :=
  match Program.dispatch B1 B2 r.call with
  | none => frame []
  | some p => frame (frame ((nativeTestFlags r.tests
      (List.replicate (paddedCount r.call.n p.1.k) true)).take (centerCount r.call.n p.1.k)))

/-- `prop:time`, paper/paper.tex: the actual
cold bitmap clock includes its full preparation parser, every signed
test and the one final output frame, with a constant default branch. -/
noncomputable def BitmapRequest.sourceSteps {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) : ℕ :=
  match Program.dispatch B1 B2 r.call with
  | none => 10
  | some p => 3*preparedFoldCost r.call p.1 (StageCertTests.scheduleHint p.1)
      (Program.witnessPrefix r.call p.1 r.witness) r.tests+13

end NearQuarticWires.StageCertificateControl
