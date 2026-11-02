import Proof.Quartic.StageMainMask.EntryPointCore
import Proof.Quartic.StageMainMask.WitnessLength

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
all original points and source records are retained together with the
runtime lengths needed for the actual ordinary subroutine input writers. -/
structure EntryCallReady {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  points : EntryPointState r a
  preparedLength : a.env 39 = (Program.prepWord B1 B2 r.call r.witness).length
  callLength : a.env 40 = (callWord r.call).length
  witnessLength : a.env 42 = (Program.witnessPrefix r.call r.selected.1 r.witness).length

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
source-length records are read physically and the literal witness-frame
payload length is computed before writing any subroutine request. -/
def makeEntryCallReady : St VV MM := .seq loadLengthRecords decodeWitnessLength

/-- `prop:time`, paper/paper.tex: all source-length
lookups and arithmetic preserve the original point and source fields
outside these exact memory-access and runtime-length variables. -/
def callReadyScratch : List (Fin VV) := lengthLoadScratch ++ [42]

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the actual source-length records yield all
request-copy lengths with a constant source clock, preserving every
computed point, original record and selected population parameter. -/
theorem makeEntryCallReady_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryPointState r a) (hfit : 2 < 2 ^ C.Wd) :
    Hs C makeEntryCallReady a 120 (fun b => EntryCallReady r b ∧ b.ip = a.ip ∧ b.out = a.out ∧
      Cst b ∧ (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc)) := by
  have hcursor : a.rc entryLengthStore ≤ 3 := by
    simpa only [ha.lengths, List.length_cons, List.length_nil] using ha.cursors entryLengthStore
  obtain ⟨b, n1, he1, hn1, hbprep, hbcall, hbhead, _hbrc7, hbrest, hbc, hbfr⟩ :=
    loadLengthRecords_run C a hc _ _ _ ha.lengths hfit
  have hframe : (Program.prepWord B1 B2 r.call r.witness).length =
      (preparedPrefixWord r.call r.selected.1).length +
        2 * (Program.witnessPrefix r.call r.selected.1 r.witness).length + 1 := by
    rw [prepWord_eq_compact r.dispatched]
    simp only [compactInput, List.length_append, frame_length]
    omega
  obtain ⟨d, n2, he2, hn2, hdwit, hdsh, hdc, hdfr⟩ :=
    decodeWitnessLength_run C b hbc _ _ _ hbprep hbhead hframe
  have hs := Same.of_sh hdsh
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hbrest
  have hbip : b.ip = a.ip := congrArg (fun t => t.1) hbrest
  have hbout : b.out = a.out := congrArg (fun t => t.2.1) hbrest
  have hbstreams : (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) :=
    congrArg (fun t => (t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2)) hbrest
  have hf : Fr a d callReadyScratch :=
    (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hdfr.weaken (fun _ hx => List.mem_append_right _ hx))
  have hqram : d.ram = a.ram := hs.ram.trans hbram
  have hq : PointData d (entryPointRequest r true true) :=
    ⟨hdc, fun i => (hf _ (by fin_cases i <;> decide)).trans (ha.pointData.fields i),
      (hf _ (by decide)).trans ha.pointData.useLeft, (hf _ (by decide)).trans ha.pointData.useRight,
      (hf _ (by decide)).trans ha.pointData.half, (hf _ (by decide)).trans ha.pointData.blockWidth,
      (hf _ (by decide)).trans ha.pointData.radix⟩
  have hdpoints : EntryPointState r d :=
    ⟨hqram ▸ ha.prepared, hqram ▸ ha.originalCall, hqram ▸ ha.witness, hqram ▸ ha.lengths,
      he2.rc_le (he1.rc_le ha.cursors), hq,
      (hf _ (by decide)).trans ha.center, (hf _ (by decide)).trans ha.leftCorner,
      (hf _ (by decide)).trans ha.rightCorner, (hf _ (by decide)).trans ha.bothCorner,
      (hf _ (by decide)).trans ha.cutoff, (hf _ (by decide)).trans ha.offset⟩
  have hdstreams : (d.kin, d.kout, d.kc) = (a.kin, a.kout, a.kc) := by
    rw [hs.kin, hs.kout, hs.kc, hbstreams]
  unfold makeEntryCallReady
  exact ⟨d, n1 + n2 + 1, Ex.seq he1 he2, by omega,
    ⟨hdpoints, (hdfr _ (by decide)).trans hbprep, (hdfr _ (by decide)).trans hbcall, hdwit⟩,
    hs.ip.trans hbip, hs.out.trans hbout, hdc, hdstreams⟩

end NearQuarticWires.StageMainMask
