import Proof.Quartic.StageMainMask.EntryArity

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the complete numeric point header is retained from the original call,
selected parameter records, witness translation and actual suffix fields. -/
structure EntryHeader {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  indices : EntryIndices r a
  scalars : EntryScalars a r.selected.1
  arity : a.env 20 = r.call.n

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
selected original scalar fields and original-call arity are read by
actual finite-memory parsers before point construction. -/
def loadEntryHeader : St VV MM := .seq loadEntryScalars readEntryArity

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: every selected-header source read is charged;
the actual column, projected sample and translation are preserved. -/
theorem loadEntryHeader_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryIndices r a)
    (hfit : 10 < 2 ^ C.Wd) (hwidth : natBitLength r.call.n + 2 ≤ C.Wd) :
    Hs C loadEntryHeader a
      (a.rc parameterStore + (callWord r.call).length + 30 * natBitLength r.call.n + 443)
      (fun b => EntryHeader r b ∧ b.ip = a.ip ∧ b.out = a.out ∧ Cst b ∧ b.ram = a.ram ∧
        (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc)) := by
  obtain ⟨b, n1, he1, hn1, hbs, hbrest, hbc, hbfr⟩ :=
    loadEntryScalars_run C r.selected.1 a hc ha.source.parameters hfit
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hbrest
  have hbip : b.ip = a.ip := congrArg (fun t => t.1) hbrest
  have hbout : b.out = a.out := congrArg (fun t => t.2.1) hbrest
  have hbsource : EntrySourceData r b :=
    ⟨hbram ▸ ha.source.originalCall, hbram ▸ ha.source.parameters,
      hbram ▸ ha.source.witness, he1.rc_le ha.source.cursors,
      (hbfr _ (by decide)).trans ha.source.translation⟩
  have hbi : EntryIndices r b := ⟨hbsource,
    (hbfr _ (by decide)).trans ha.column, (hbfr _ (by decide)).trans ha.fieldValue,
    (hbfr _ (by decide)).trans ha.translation⟩
  obtain ⟨d, n2, he2, hn2, hdarity, hdi, hdip, hdout, hdc, hdfr, hdram, hdstreams⟩ :=
    readEntryArity_run C r b hbc hbi hwidth
  have hds : EntryScalars d r.selected.1 :=
    ⟨(hdfr _ (by decide)).trans hbs.blocks, (hdfr _ (by decide)).trans hbs.syndrome,
      (hdfr _ (by decide)).trans hbs.blockSize, (hdfr _ (by decide)).trans hbs.samplerSide,
      (hdfr _ (by decide)).trans hbs.populationThreshold, (hdfr _ (by decide)).trans hbs.witnessOffset⟩
  unfold loadEntryHeader
  exact ⟨d, n1 + n2 + 1, Ex.seq he1 he2, by omega,
    ⟨hdi, hds, hdarity⟩, hdip.trans hbip, hdout.trans hbout, hdc, hdram.trans hbram,
    hdstreams.trans (congrArg (fun t => (t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2)) hbrest)⟩

end NearQuarticWires.StageMainMask
