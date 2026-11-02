import Proof.Quartic.StageMainMask.SizedAcquire
import Proof.Quartic.StageMainMask.EntryMetadata

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual entry retains its complete finite sources, measured lengths,
original population cutoff and four physically computed packed points. -/
structure EntryPointState {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  prepared : a.ram compactStore = (Program.prepWord B1 B2 r.call r.witness).map Bool.toNat
  originalCall : a.ram callStore = (callWord r.call).map Bool.toNat
  witness : a.ram witnessStore = (Program.witnessPrefix r.call r.selected.1 r.witness).map Bool.toNat
  lengths : a.ram entryLengthStore =
    [(Program.prepWord B1 B2 r.call r.witness).length, (callWord r.call).length,
      (preparedPrefixWord r.call r.selected.1).length]
  cursors : ∀ store, a.rc store ≤ (a.ram store).length
  pointData : PointData a (entryPointRequest r true true)
  center : a.env 114 = (entryPointRequest r false false).packed
  leftCorner : a.env 115 = (entryPointRequest r true false).packed
  rightCorner : a.env 116 = (entryPointRequest r false true).packed
  bothCorner : a.env 117 = (entryPointRequest r true true).packed
  cutoff : a.env 36 = r.selected.1.tau
  offset : a.env 38 = r.selected.1.k

/-- Step 4 of `sec:algorithm`, `imp:partition` and `imp:seed`,
paper/paper.tex: the actual
entry body acquires its original source, decodes the sample and computes
every original coordinate of all four canonical affine corners. -/
def entryPointCore : St VV MM := .seq acquireSizedEntrySource
  (.seq readEntryIndices (.seq loadEntryHeader (.seq entryPointMetadata produceFourCorners)))

/-- `prop:time`, paper/paper.tex: finite source
measurement, all metadata parsing and the four actual point encoders
are included before any original gate or mask is evaluated. -/
noncomputable def entryPointCoreSteps {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  sizedEntrySourceSteps r + StageGamma.readFieldsCost [r.column.val, r.fieldValue.val] +
    (callWord r.call).length + 30 * natBitLength r.call.n + 20 * r.call.n +
    4 * pointCornerCost (entryPointRequest r false false) + 600

/-- Step 4 of `sec:algorithm`, `imp:partition`, `imp:seed` and
`prop:time`, paper/paper.tex: the literal entry source physically determines its retained
sources, cutoff and four original point codes from empty stores. No
point, initialized metadata or decoded circuit values are supplied. -/
theorem entryPointCore_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = entryWord r ++ rest)
    (hwidth : (entryWord r).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd)
    (hnwidth : r.call.n + 4 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C entryPointCore a (entryPointCoreSteps r) (fun b =>
      EntryPointState r b ∧ b.ip = a.ip + (entryWord r).length ∧ b.out = a.out ∧
      Cst b ∧ (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc)) := by
  obtain ⟨b, n1, he1, hn1, hbsource, hbip, hbout, hbc, hbstreams⟩ :=
    acquireSizedEntrySource_run C r rest a hc hin hwidth h64 hnwidth hempty
  have hbin : C.inp.drop b.ip = natWord r.column.val ++ natWord r.fieldValue.val ++ rest := by
    rw [hbip, ← List.drop_drop, hin, entryWord]
    simp only [List.append_assoc, List.drop_left]
  have hfieldwidth : natBitLength r.column.val + 2 ≤ C.Wd ∧
      natBitLength r.fieldValue.val + 2 ≤ C.Wd := by
    have hu := NearCubicGates.Close.Dispatch.natBitLength_le_len r.column.val
    have hv := NearCubicGates.Close.Dispatch.natBitLength_le_len r.fieldValue.val
    simp only [entryWord, List.length_append] at hwidth
    constructor <;> omega
  obtain ⟨c, n2, he2, hn2, hci, hcip, hcout, hcc, hcram, hcstreams⟩ :=
    readEntryIndices_run C r rest b hbc hbsource.source hbin hfieldwidth
  have hcparam : c.rc parameterStore ≤ 46 := by
    simpa only [hci.source.parameters, parameterScalars_length] using hci.source.cursors parameterStore
  have hNwidth : natBitLength r.call.n + 2 ≤ C.Wd := by
    have hh := Nat.log_le_self 2 r.call.n
    unfold natBitLength
    omega
  obtain ⟨d, n3, he3, hn3, hdheader, hdip, hdout, hdc, hdram, hdstreams⟩ :=
    loadEntryHeader_run C r c hcc hci (lt_trans (by omega) Nat.lt_two_pow_self) hNwidth
  obtain ⟨e, n4, he4, hn4, hedata, hesh, hefr⟩ := entryPointMetadata_run C r d hdc hdheader hnwidth
  obtain ⟨f, n5, he5, hn5, hfc, hfcu, hfcv, hfcuv, hfdata, hfsh, hffr⟩ :=
    produceFourCorners_run C (entryPointRequest r false false) e hedata hnwidth
  have hsame : Same d f := Same.of_sh (hfsh.trans hesh)
  have hfram : f.ram = b.ram := hsame.ram.trans (hdram.trans hcram)
  have hfstate : EntryPointState r f := by
    refine ⟨hfram ▸ hbsource.prepared, hfram ▸ hbsource.source.originalCall,
      hfram ▸ hbsource.source.witness, hfram ▸ hbsource.lengths, ?_, hfdata,
      hfc, hfcu, hfcv, hfcuv, ?_, ?_⟩
    · intro store
      rw [hsame.ram, hsame.rc]
      exact hdheader.indices.source.cursors store
    · exact (hffr _ (by decide)).trans ((hefr _ (by decide)).trans hdheader.scalars.populationThreshold)
    · exact (hffr _ (by decide)).trans ((hefr _ (by decide)).trans hdheader.scalars.witnessOffset)
  have hfstreams : (f.kin, f.kout, f.kc) = (a.kin, a.kout, a.kc) := by
    rw [hsame.kin, hsame.kout, hsame.kc, hdstreams, hcstreams, hbstreams]
  unfold entryPointCore
  refine ⟨f, n1 + (n2 + (n3 + (n4 + n5 + 1) + 1) + 1) + 1,
    Ex.seq he1 (Ex.seq he2 (Ex.seq he3 (Ex.seq he4 he5))), ?_, hfstate, ?_,
    hsame.out.trans (hdout.trans (hcout.trans hbout)), hfdata.constants, hfstreams⟩
  · unfold entryPointCoreSteps
    omega
  · rw [hsame.ip, hdip, hcip, hbip]
    simp only [entryWord, List.length_append]
    omega

end NearQuarticWires.StageMainMask
