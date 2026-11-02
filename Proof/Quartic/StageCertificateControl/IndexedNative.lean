import Proof.Quartic.StageCertificateControl.IndexedFrontMachine
import Proof.Quartic.StageCertificateControl.NativePrefixMachine
import Proof.Quartic.Program.Pipe

/-!
# Complete physical indexing and threshold prefixing for native tables

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
`lem:print`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertTests

/-- `prop:time`, paper/paper.tex: the real
indexed native provider pays actual cold indexing, retained binary
threshold prefixing, and the complete two-machine composition. -/
noncomputable def indexedNativeBudget {B1 B2 : ℕ} (baseBudget : IndexedRequest B1 B2→ℕ)
    (r : IndexedRequest B1 B2) : ℕ :=
  4*indexedFrontBudget r+4*nativePrefixBudget r.metadata.threshold r.baseWord.length (baseBudget r)+12

/-- `sec:algorithm`, `lem:print`, and `prop:time`, paper/paper.tex: a real whole-table
base word function is physically composed with original-source index
selection and binary threshold retention. Its native q-header and
entire signed output body remain unchanged after the actual threshold
codec, without any supplied decoded record or numeric threshold read. -/
noncomputable def indexedNativeWordFunction (B1 B2 : ℕ)
    {payload : IndexedRequest B1 B2→List Bool} {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (payload r)) baseBudget) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.word
      (fun r => frame (RepairRepresentation.natWord r.metadata.threshold++payload r))
      (indexedNativeBudget baseBudget) :=
  Program.WordFunction.pipe (indexedFrontWordFunction B1 B2)
    (nativePrefixWordFunction base (fun r => r.metadata.threshold))

/-- `prop:time`, paper/paper.tex: physical
indexing and threshold prefixing add original-call polynomial work and
only a fixed linear multiplier of the actual whole native budget. The
bound is uniform over every witness and every actual test index. -/
theorem indexedNativeBudget_linear (B1 B2 : ℕ) (baseBudget : IndexedRequest B1 B2→ℕ) :
    ∃ K e : ℕ, ∀ r : IndexedRequest B1 B2,
      indexedNativeBudget baseBudget r≤80008*baseBudget r+K*((callWord r.prepared.call).length+1)^e := by
  have hM := indexedSourceMass_polynomial B1 B2
  have hF := ((PreparedPolynomial.const (2*10000000)).mul (hM.pow 2)).add (PreparedPolynomial.const 2)
  have hS := (PreparedPolynomial.const 80008).mul
    (((PreparedPolynomial.const 4).mul hM).add (PreparedPolynomial.const 1))
  have hp := (((PreparedPolynomial.const 4).mul hF).add hS).add (PreparedPolynomial.const 12)
  obtain ⟨K,e,hK⟩ := hp
  refine ⟨K,e,fun r => ?_⟩
  have hl := nativePrefixBudget_linear r.metadata.threshold r.baseWord.length (baseBudget r)
  have hbytes := r.byte_bounds.2
  simp only [IndexedRequest.frontWord,List.length_append] at hbytes
  have ho := hK r.prepared
  unfold indexedNativeBudget indexedFrontBudget indexedFrontSourceSteps
  nlinarith

end NearQuarticWires.StageCertificateControl
