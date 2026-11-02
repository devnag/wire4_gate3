import Proof.Quartic.StageMainMask.CallReady
import Proof.Quartic.StageMainMask.EntryRequests
import Proof.Quartic.StageMainMask.NaturalFields

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the original finite source records and actual computed scalar fields
needed by the three numeric-entry subroutine requests. -/
structure EntryNumericData {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  prepared : a.ram compactStore = (Program.prepWord B1 B2 r.call r.witness).map Bool.toNat
  originalCall : a.ram callStore = (callWord r.call).map Bool.toNat
  witness : a.ram witnessStore = (Program.witnessPrefix r.call r.selected.1 r.witness).map Bool.toNat
  preparedLength : a.env 39 = (Program.prepWord B1 B2 r.call r.witness).length
  callLength : a.env 40 = (callWord r.call).length
  witnessLength : a.env 42 = (Program.witnessPrefix r.call r.selected.1 r.witness).length
  left : a.env 27 = (entryPosition r).1.val
  right : a.env 28 = (entryPosition r).2.val
  corners : ∀ i : Fin 4, a.env (cornerRegister i) = entryCorners r i
  cutoff : a.env 36 = r.selected.1.tau
  offset : a.env 38 = r.selected.1.k

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual source-acquisition and four-point computation supply all
subroutine request data, rather than a decoded-point hypothesis. -/
theorem EntryCallReady.source {B1 B2 : ℕ} {r : EntryRequest B1 B2} {a : DS VV MM}
    (h : EntryCallReady r a) : EntryNumericData r a := by
  refine ⟨h.points.prepared, h.points.originalCall, h.points.witness,
    h.preparedLength, h.callLength, h.witnessLength, ?_, ?_, ?_, h.points.cutoff, h.points.offset⟩
  · exact h.points.pointData.fields ⟨7, by decide⟩
  · exact h.points.pointData.fields ⟨8, by decide⟩
  · intro i
    fin_cases i
    · exact h.points.center
    · exact h.points.leftCorner
    · exact h.points.rightCorner
    · exact h.points.bothCorner

/-- `prop:time`, paper/paper.tex: the physical
request writers use only these fixed printer and copy variables. -/
def sourceWriterScratch : List (Fin VV) := [c0, t0, t3] ++ emitNatT

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
binary request printing preserves every actual source record and
computed original point outside its fixed scalar scratch variables. -/
theorem EntryNumericData.of_writer {B1 B2 : ℕ} {r : EntryRequest B1 B2}
    {a b : DS VV MM} (h : EntryNumericData r a) (hram : b.ram = a.ram)
    (hf : Fr a b sourceWriterScratch) : EntryNumericData r b := by
  refine ⟨hram ▸ h.prepared, hram ▸ h.originalCall, hram ▸ h.witness,
    (hf _ (by decide)).trans h.preparedLength, (hf _ (by decide)).trans h.callLength,
    (hf _ (by decide)).trans h.witnessLength, (hf _ (by decide)).trans h.left,
    (hf _ (by decide)).trans h.right, ?_,
    (hf _ (by decide)).trans h.cutoff, (hf _ (by decide)).trans h.offset⟩
  intro i
  exact (hf _ (by fin_cases i <;> decide)).trans (h.corners i)

end NearQuarticWires.StageMainMask
