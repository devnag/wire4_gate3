import Proof.Quartic.StageMainMask.FourCorners
import Proof.Quartic.StageMain.EntryCoordinates
import Proof.Quartic.Builder.CenterForm
import Proof.Quartic.StagePrint.TranslationConnection

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces
open StageMain StagePullback

/-- `imp:partition`, `imp:seed` and Step 4 of `sec:algorithm`,
paper/paper.tex: the numeric
entry determines its canonical point metadata from the original column,
selected witness translation and actual projected sample coordinates. -/
noncomputable def entryPointRequest {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (left right : Bool) : PointRequest := by
  let hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  let P := Builder.star r.call hs
  refine ⟨P, Builder.translation r.call hs r.witness,
    ⟨r.column.val % 2 ^ PrimT.C4Geo.dRow P, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
    ⟨r.column.val / 2 ^ PrimT.C4Geo.dRow P, ?_⟩,
    Fin.cast (Builder.seedN_eq_patternCodes r.call hs) (entryPosition r).1,
    Fin.cast (Builder.seedN_eq_patternCodes r.call hs) (entryPosition r).2, left, right⟩
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
  rw [← pow_add, Nat.add_comm, ← Builder.centerCount_eq r.call hs]
  exact r.column.isLt

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: selecting no errors gives the exact
original Builder center of the sampled column. -/
theorem entryPointRequest_center {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPointRequest r false false).point =
      Builder.center r.call (Cells.prepare_spec _ r.selected.1 r.selected.2) r.witness r.column := by
  funext x
  simp only [entryPointRequest, PointRequest.point, Bool.false_and, Bool.xor_false]
  rfl

/-- `imp:partition`, `imp:seed` and Step 4 of `sec:algorithm`,
paper/paper.tex: selecting both
errors gives the exact original sampled point, in canonical pattern order. -/
theorem entryPointRequest_both {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPointRequest r true true).point =
      (Builder.star r.call (Cells.prepare_spec _ r.selected.1 r.selected.2)).point
        (Builder.center r.call (Cells.prepare_spec _ r.selected.1 r.selected.2) r.witness r.column)
        (Builder.pattern r.call (Cells.prepare_spec _ r.selected.1 r.selected.2) (entryPosition r).1)
        (Builder.pattern r.call (Cells.prepare_spec _ r.selected.1 r.selected.2) (entryPosition r).2) := by
  funext x
  simp only [entryPointRequest, PointRequest.point, Bool.true_and]
  rfl

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the physically generated fourth corner has precisely the predicate
value required by the original Main numeric-entry contract. -/
theorem entryPointRequest_predicate {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    r.call.predicate (entryPointRequest r true true).point = entryPredicate r := by
  rw [entryPointRequest_both]
  rfl

/-- Witness (W1), `imp:partition` and Step 4 of `sec:algorithm`,
paper/paper.tex: the point
translation code is exactly the physical retained-witness prefix value. -/
theorem entryPointRequest_translation {B1 B2 : ℕ} (r : EntryRequest B1 B2) (left right : Bool) :
    translationNumber (entryPointRequest r left right).parameters
      (entryPointRequest r left right).translation =
      StagePrint.Header.binaryPrefix (Program.witnessPrefix r.call r.selected.1 r.witness)
        r.selected.1.k :=
  StagePrint.Header.translationNumber_retained r.call
    (Cells.prepare_spec _ r.selected.1 r.selected.2) r.witness

end NearQuarticWires.StageMainMask
