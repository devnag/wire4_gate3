import Proof.Quartic.StageMainMask.EntryPoints
import Proof.Quartic.StageMainMask.EntryScalars
import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StagePrint.TranslationInit
import Proof.Gates.Cells.Inv

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift StagePullback

/-- Step 4 of `sec:algorithm` and witness (W1), paper/paper.tex: the actual retained source contains the
original call, complete selected parameters and finite padded witness,
with the canonical translation physically computed from its W1 bits. -/
structure EntrySourceData {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  originalCall : a.ram callStore = (callWord r.call).map Bool.toNat
  parameters : a.ram parameterStore = parameterScalars r.selected.1
  witness : a.ram witnessStore =
    (Program.witnessPrefix r.call r.selected.1 r.witness).map Bool.toNat
  cursors : ∀ store, a.rc store ≤ (a.ram store).length
  translation : a.env StagePrint.Header.translation =
    translationNumber (entryPointRequest r false false).parameters
      (entryPointRequest r false false).translation

/-- Step 4 of `sec:algorithm` and witness (W1), paper/paper.tex: the preparation parser runs before the
paid original-witness translation reader, without predecoded source data. -/
def acquireEntrySource : St VV MM := .seq initializeCompact StagePrint.Header.readTranslation

/-- `prop:time`, paper/paper.tex: source acquisition
and the actual finite W1 memory-prefix loop are both included. -/
noncomputable def acquireEntrySourceSteps {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  initializeCost r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)
    (compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)).length +
  107 + StagePrint.Header.translationCost
    (Program.witnessPrefix r.call r.selected.1 r.witness).length r.selected.1.k

/-- Step 4 of `sec:algorithm`, witness (W1) and `prop:time`,
paper/paper.tex: the actual
entry source supplies all retained records and its exact canonical
translation from empty stores, stopping before the two numeric indices. -/
theorem acquireEntrySource_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = entryWord r ++ rest)
    (hwidth : (entryWord r).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd)
    (hnwidth : r.call.n + 4 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C acquireEntrySource a (acquireEntrySourceSteps r) (fun b =>
      EntrySourceData r b ∧
      b.ip = a.ip + (Program.prepWord B1 B2 r.call r.witness).length ∧ b.out = a.out ∧ Cst b) := by
  let witness := Program.witnessPrefix r.call r.selected.1 r.witness
  let prep := compactInput r.call r.selected.1 witness
  have hlayout : entryWord r = prep ++ natWord r.column.val ++ natWord r.fieldValue.val := by
    rw [entryWord, prepWord_eq_compact r.dispatched]
  have hpwidth : prep.length + 2 ≤ C.Wd := by
    rw [hlayout] at hwidth
    simp only [List.length_append] at hwidth
    omega
  obtain ⟨hprefix, hfit, hbits, hprime, hfactor⟩ :=
    compact_decoder_bounds r.call r.selected.1 witness C.Wd hpwidth
  obtain ⟨b, n1, he1, hn1, hbip, hbdata, _hblen, _hbram, _hbrc, hbrest, hbc, _hbfr⟩ :=
    initialize_run C r.call r.selected.1 prep.length witness
      (natWord r.column.val ++ natWord r.fieldValue.val ++ rest) a hc
      (by simpa only [hlayout, List.append_assoc] using hin)
      hprefix hfit hbits hpwidth ⟨hprime, hfactor⟩ (fun store _ => hempty store)
  have hcursor : ∀ store, b.rc store ≤ (b.ram store).length :=
    he1.rc_le (by intro store; rw [(hempty store).1, (hempty store).2]; rfl)
  have hbparam : b.rc parameterStore ≤ 46 := by
    simpa only [hbdata.scalarFields, parameterScalars_length] using hcursor parameterStore
  have hbwit : b.rc witnessStore ≤ witness.length := by
    simpa only [hbdata.witnessBits, List.length_map] using hcursor witnessStore
  have hk := (Cells.prepare_spec _ r.selected.1 r.selected.2).k_lt_n
  change r.selected.1.k < r.call.n at hk
  have hwlen : r.selected.1.k ≤ witness.length := by
    simp only [witness, Program.witnessPrefix, List.length_ofFn, Program.witnessReadLength]
    omega
  have htrans := StagePrint.Header.readTranslation_run C r.selected.1 witness b hbc
    hbdata.scalarFields hbdata.witnessBits hwlen
    (Nat.pow_lt_pow_right (by decide) (by omega))
    (lt_trans (by omega) Nat.lt_two_pow_self)
  obtain ⟨d, n2, he2, hn2, hdvalue, hdram, hdip, hdout, _hdstreams, hdc⟩ := htrans
  have hbudget : n2 ≤ 106 + StagePrint.Header.translationCost witness.length r.selected.1.k := by
    apply hn2.trans
    unfold StagePrint.Header.translationCost
    nlinarith
  have hddata : EntrySourceData r d := by
    refine ⟨hdram ▸ hbdata.originalCall, hdram ▸ hbdata.scalarFields,
      hdram ▸ hbdata.witnessBits, he2.rc_le hcursor, ?_⟩
    exact hdvalue.trans (entryPointRequest_translation r false false).symm
  have hbout : b.out = a.out := congrArg (fun t => t.1) hbrest
  unfold acquireEntrySource
  refine ⟨d, n1 + n2 + 1, Ex.seq he1 he2, ?_, hddata, ?_, hdout.trans hbout, hdc⟩
  · change n1 + n2 + 1 ≤ initializeCost r.call r.selected.1 witness prep.length +
      107 + StagePrint.Header.translationCost witness.length r.selected.1.k
    omega
  · rw [hdip, hbip, prepWord_eq_compact r.dispatched]

end NearQuarticWires.StageMainMask
