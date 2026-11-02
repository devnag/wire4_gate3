import Proof.Quartic.StageMainMask.StructuralRaw
import Proof.Quartic.StageMain.EntryRequest
import Proof.Quartic.StageCert.StructuralBuilder
import Proof.Quartic.Cells.ParametersCallEncoding

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `def:mask` and `sec:algorithm`, paper/paper.tex: one original prepared call and two actual cell-side
indices determine the shared structural-source request. -/
structure StructuralRequest (B1 B2 : ℕ) where
  call : Call
  selected : Program.Selected call
  dispatched : Program.dispatch B1 B2 call = some selected
  witness : List Bool
  left : Fin (Program.runCall call selected witness).seed.N
  right : Fin (Program.runCall call selected witness).seed.N

/-- `def:mask`, paper/paper.tex: the shared source
word is exactly the finite preparation word followed by the two binary
pattern codes, with no center or incidence vector supplied. -/
noncomputable def structuralWord {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : List Bool :=
  Program.prepWord B1 B2 r.call r.witness ++ natWord r.left.val ++ natWord r.right.val

/-- `def:mask`, paper/paper.tex: the shared flag
is the original structural mask, which is independent of the original
column and its center. -/
noncomputable def structuralBit {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : Bool :=
  ((Program.runCall r.call r.selected r.witness).column
    ⟨0, Nat.two_pow_pos _⟩).structural (r.left, r.right)

/-- `def:mask`, paper/paper.tex: the concrete
one-bit reply uses the same literal framing for every original pair. -/
noncomputable def structuralOutput {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : List Bool :=
  frame [structuralBit r]

/-- `def:mask`, paper/paper.tex: the selected
original parameters provide the internal finite source request with
the identical canonical numeric pattern codes. -/
noncomputable def structuralRawRequest {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    StructuralRawRequest where
  call := r.call
  partition := Builder.star r.call (Cells.prepare_spec _ r.selected.1 r.selected.2)
  arity := rfl
  arity_le_call := Cells.dispatched_n_le_callWord r.dispatched
  threshold := r.selected.1.dstar
  left := StageCert.builderPatternIndex r.call
    (Cells.prepare_spec _ r.selected.1 r.selected.2) r.left
  right := StageCert.builderPatternIndex r.call
    (Cells.prepare_spec _ r.selected.1 r.selected.2) r.right

/-- `def:mask`, paper/paper.tex: the exact raw
source procedure's flag is the literal selected original structural
mask, with no change to its canonical pattern order. -/
theorem structuralRawRequest_bit {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    (structuralRawRequest r).bit = structuralBit r :=
  (StageCert.builder_structural_eq_numeric r.call
    (Cells.prepare_spec _ r.selected.1 r.selected.2) r.witness
    ⟨0, Nat.two_pow_pos _⟩ r.left r.right).symm

/-- `def:mask`, paper/paper.tex: the shared
structural-source reply is valid at every original column of the call. -/
theorem structuralBit_eq_column {B1 B2 : ℕ} (r : StructuralRequest B1 B2)
    (z : Fin (2 ^ (r.call.n - r.selected.1.k))) :
    ((Program.runCall r.call r.selected r.witness).column z).structural (r.left, r.right) =
      structuralBit r := rfl

end NearQuarticWires.StageMainMask
