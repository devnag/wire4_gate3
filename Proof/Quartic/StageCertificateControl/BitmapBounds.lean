import Proof.Quartic.StageCertificateControl.BitmapScalarMass
import Proof.Quartic.StageCertificateControl.BitmapMachine

/-!
# Actual scalar bounds for the signed native bitmap

Paper: `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CellsPack (Gof)
open StageCertTests (PreparedScheduleRequest)

/-- `prop:time`, paper/paper.tex: these are
bounds on actual scalar values and encoded source lengths, excluding
the native column census and the native bitmap itself. -/
structure BitmapScalarBounds {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call) (M : ℕ) : Prop where
  positive : 10≤M
  call : (callWord r.call).length+1≤M
  arity : r.call.n+1≤M
  reader : StageLift.parameterReadCost p.1 (StageCertTests.scheduleHint p.1)≤M
  witness : (Program.witnessPrefix r.call p.1 r.witness).length≤M
  preparation : (Program.prepWord B1 B2 r.call r.witness).length≤M
  count : r.tests.length+1≤M
  width : ∀test∈r.tests,test.width+1≤M
  threshold : ∀test∈r.tests,natBitLength test.bound≤M
  compilation : Gof StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) (leadOnes r.word)≤M

/-- `sec:params`, `sec:algorithm`, and `prop:time`, paper/paper.tex: the original literal arity
header is unchanged by appending all actual signed native tables. -/
theorem BitmapRequest.leading_selected {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) :
    leadOnes r.word=1+natBitLength r.call.n := by
  rw [r.word_selected p hd]
  simpa only [List.append_assoc] using StageMain.taggedCall_header_width r.call
    (Program.parametersWord p.1++frame (Program.witnessPrefix r.call p.1 r.witness)++
      RepairRepresentation.natWord r.tests.length++nativeTestStream r.tests)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: every scalar bitmap bound follows from the
actual dispatched preparation and physically supplied native records.
No stage execution or runtime bound is assumed. -/
theorem bitmapScalar_bounds {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) :
    BitmapScalarBounds r p (bitmapScalarMass coefficient degree
      (PreparedScheduleRequest.mk r.call r.witness p hd)) := by
  let s := PreparedScheduleRequest.mk r.call r.witness p hd
  let M := bitmapScalarMass coefficient degree s
  change BitmapScalarBounds r p M
  have hsword : s.word=true::(callWord r.call++Program.parametersWord p.1++
      frame (Program.witnessPrefix r.call p.1 r.witness)) := s.word_eq
  have hM : M=StageCertTests.prepScheduleMass r.call p.1+s.word.length+
      (StageCertTests.certificateMetadata p.1 r.call.kind).length+
      coefficient*(r.call.n+1)^degree+
      Gof StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) (leadOnes s.word)+10 := rfl
  have hcall : (callWord r.call).length+1≤M := by
    rw [hM]
    unfold StageCertTests.prepScheduleMass
    omega
  have hhead : leadOnes s.word=1+natBitLength r.call.n := by
    rw [hsword]
    simpa only [List.append_assoc] using StageMain.taggedCall_header_width r.call
      (Program.parametersWord p.1++frame (Program.witnessPrefix r.call p.1 r.witness))
  have hwitness : (Program.witnessPrefix r.call p.1 r.witness).length ≤ s.word.length := by
    rw [hsword]
    simp only [List.length_cons,List.length_append,frame_length]
    omega
  have hcount := r.count_selected p hd
  have hprep : s.word=Program.prepWord B1 B2 r.call r.witness := rfl
  refine ⟨?_,hcall,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hM];omega
  · have hn := Cells.dispatched_n_le_callWord hd
    omega
  · rw [hM]
    unfold StageCertTests.prepScheduleMass
    omega
  · rw [hM]
    omega
  · rw [hM,← hprep]
    omega
  · rw [hM,hcount]
    omega
  · intro test ht
    have hw := r.widths test ht
    rw [hM]
    omega
  · intro test ht
    have hb := r.threshold_bits p hd test ht
    rw [hM]
    unfold StageCertTests.prepScheduleMass
    omega
  · rw [r.leading_selected p hd,← hhead,hM]
    omega

end NearQuarticWires.StageCertificateControl
