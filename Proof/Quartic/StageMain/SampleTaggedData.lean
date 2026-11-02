import Proof.Quartic.StageMain.TaggedWordFunction
import Proof.Quartic.StageMain.SampleWordFunction
import Proof.Gates.Cells.Lang

/-!
# The sampler branch of the main-pass call interface

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: the sampler is the first branch of
a fixed ordinary selector. Its call budget includes the tag, copied
coefficient records, polynomial execution and framed field answer.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

variable {Req : Type} {input output : Req → List Bool} {budget : Req → ℕ}

def samplePayload (r : SampleRequest) : List Bool :=
  binary r.ell (JoinElimination.gen r.modulus r.ell 8 r.seed r.label)

noncomputable def sampleTaggedCallee
    (f : WordFunction Req input (fun r => frame (output r)) budget) : Callee where
  Req := SampleRequest ⊕ Req
  inw := Tagged.taggedInput sampleRawWord input
  outw := fun r => frame (Tagged.taggedAnswer samplePayload output r)
  bud := Tagged.taggedCost sampleRawWord samplePayload input output sampleRawBudget budget
  wf := Tagged.taggedWordFunction sampleRawWordFunction f

theorem sampleTaggedCallee_input
    (f : WordFunction Req input (fun r => frame (output r)) budget) (r : SampleRequest) :
    (sampleTaggedCallee f).inw (.inl r) = false :: sampleRawWord r := rfl

theorem sampleTaggedCallee_output
    (f : WordFunction Req input (fun r => frame (output r)) budget) (r : SampleRequest) :
    (sampleTaggedCallee f).outw (.inl r) = sampleRawOutput r := rfl

theorem sampleTaggedCallee_budget
    (f : WordFunction Req input (fun r => frame (output r)) budget) (r : SampleRequest) :
    (sampleTaggedCallee f).bud (.inl r) ≤ 30000000 * (r.ell + 1) ^ 2 := by
  have hin := sampleRawWord_length r
  have htime := sampleRawBudget_le r
  change 200 * ((sampleRawWord r).length + (samplePayload r).length + sampleRawBudget r + 1) + 12 ≤ _
  simp only [samplePayload, SignedSortKey.binary_length]
  nlinarith

end NearQuarticWires.StageMain
