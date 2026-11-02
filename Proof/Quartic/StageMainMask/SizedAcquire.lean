import Proof.Quartic.StageMainMask.RecordLengths
import Proof.Quartic.StageLift.StoreFrame

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageMain.CallSkip StageLift

private def storeOpDecidable {V M : ℕ} (store : Fin M) (op : Op V M) :
    Decidable (avoidsStoreOp store op) := by
  cases op <;> dsimp only [avoidsStoreOp] <;> infer_instance

private def storeDecidable {V M : ℕ} (store : Fin M) :
    (s : St V M) → Decidable (avoidsStore store s)
  | .op op => storeOpDecidable store op
  | .seq s t => @instDecidableAnd _ _ (storeDecidable store s) (storeDecidable store t)
  | .ite _ s t => @instDecidableAnd _ _ (storeDecidable store s) (storeDecidable store t)
  | .loop _ s => storeDecidable store s

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the complete finite source retains its exact literal prep bytes and a
physical three-record length ledger alongside the original call and witness. -/
structure EntryFiniteSource {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  source : EntrySourceData r a
  prepared : a.ram compactStore = (Program.prepWord B1 B2 r.call r.witness).map Bool.toNat
  lengths : a.ram entryLengthStore =
    [(Program.prepWord B1 B2 r.call r.witness).length, (callWord r.call).length,
      (preparedPrefixWord r.call r.selected.1).length]

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
actual finite-header measurement precedes retention; measured lengths
are saved before the original witness's translation is decoded. -/
def acquireSizedEntrySource : St VV MM := .seq measureEntryHeader
  (.seq initializeCompact (.seq recordEntryLengths StagePrint.Header.readTranslation))

/-- `prop:time`, paper/paper.tex: exact source
measurement, head restoration, retention, length writes and W1 decoding
are all included in the finite acquisition clock. -/
noncomputable def sizedEntrySourceSteps {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  3000 * ((callWord r.call).length + 1) ^ 3 +
    4000 * ((Program.parametersWord r.selected.1).length + 1) ^ 2 +
    5 * (preparedPrefixWord r.call r.selected.1).length + 30 +
  initializeCost r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)
    (compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)).length +
  StagePrint.Header.translationCost
    (Program.witnessPrefix r.call r.selected.1 r.witness).length r.selected.1.k + 114

/-- Step 4 of `sec:algorithm`, witness (W1) and `prop:time`,
paper/paper.tex: the original
entry input physically supplies its complete finite source and measured
length ledger from empty stores, without any source-size oracle. -/
theorem acquireSizedEntrySource_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = entryWord r ++ rest)
    (hwidth : (entryWord r).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd)
    (hnwidth : r.call.n + 4 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C acquireSizedEntrySource a (sizedEntrySourceSteps r) (fun b =>
      EntryFiniteSource r b ∧
      b.ip = a.ip + (Program.prepWord B1 B2 r.call r.witness).length ∧ b.out = a.out ∧ Cst b ∧
      (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc)) := by
  let witness := Program.witnessPrefix r.call r.selected.1 r.witness
  let prep := compactInput r.call r.selected.1 witness
  have hlayout : entryWord r = preparedPrefixWord r.call r.selected.1 ++ frame witness ++
      natWord r.column.val ++ natWord r.fieldValue.val := by
    rw [entryWord, prepWord_eq_compact r.dispatched]
    rfl
  have hpwidth : prep.length + 2 ≤ C.Wd := by
    rw [hlayout] at hwidth
    simp only [List.length_append] at hwidth
    dsimp only [prep, compactInput]
    simp only [List.length_append]
    omega
  obtain ⟨hprefix, hfit, hbits, hprime, hfactor⟩ :=
    compact_decoder_bounds r.call r.selected.1 witness C.Wd hpwidth
  obtain ⟨m, n0, he0, hn0, hm41, hmip, hmrest, hmc⟩ :=
    measureEntryHeader_run C r.call r.selected.1
    (frame witness ++ natWord r.column.val ++ natWord r.fieldValue.val ++ rest) a hc
    (by simpa only [hlayout, List.append_assoc] using hin) hprefix
  have hmram : m.ram = a.ram := congrArg (fun t => t.2.1) hmrest
  have hmrc : m.rc = a.rc := congrArg (fun t => t.2.2.1) hmrest
  have hmin : C.inp.drop m.ip = prep ++ natWord r.column.val ++ natWord r.fieldValue.val ++ rest := by
    rw [hmip, hin]
    rw [entryWord, prepWord_eq_compact r.dispatched]
  have hmempty : ∀ store, m.ram store = [] ∧ m.rc store = 0 := by
    intro store
    rw [hmram, hmrc]
    exact hempty store
  obtain ⟨b, n1, he1, hn1, hbip, hbdata, hblen, hbram6, _hbrc6, hbrest, hbc, hbfr⟩ :=
    initialize_run C r.call r.selected.1 prep.length witness
    (natWord r.column.val ++ natWord r.fieldValue.val ++ rest) m hmc
    (by simpa only [List.append_assoc] using hmin) hprefix hfit hbits hpwidth
    ⟨hprime, hfactor⟩ (fun store _ => hmempty store)
  have hb41 : b.env 41 = (preparedPrefixWord r.call r.selected.1).length :=
    (hbfr _ (by decide)).trans hm41
  have hav : avoidsStore entryLengthStore initializeCompact := by
    letI := storeDecidable entryLengthStore initializeCompact
    decide
  have hbempty : b.ram entryLengthStore = [] ∧ b.rc entryLengthStore = 0 := by
    have hh := avoidsStore_spec he1 hav
    rw [hh.1, hh.2]
    exact hmempty entryLengthStore
  obtain ⟨d, n2, he2, hn2, hdlengths, _hdrc7, hdenv, hdrest, hdother⟩ :=
    recordEntryLengths_run C b hbempty
  have hdparam : d.ram parameterStore = parameterScalars r.selected.1 :=
    (hdother _ (by decide)).1.trans hbdata.scalarFields
  have hdwit : d.ram witnessStore = witness.map Bool.toNat :=
    (hdother _ (by decide)).1.trans hbdata.witnessBits
  have hcursor : ∀ store, d.rc store ≤ (d.ram store).length := by
    have hmcur : ∀ store, m.rc store ≤ (m.ram store).length := by
      intro store
      rw [(hmempty store).1, (hmempty store).2]
      rfl
    exact he2.rc_le
      (he1.rc_le hmcur)
  have hdparamcur : d.rc parameterStore ≤ 46 := by
    simpa only [hdparam, parameterScalars_length] using hcursor parameterStore
  have hdwitcur : d.rc witnessStore ≤ witness.length := by
    simpa only [hdwit, List.length_map] using hcursor witnessStore
  have hdc : Cst d := ⟨(congrFun hdenv vZ).trans hbc.z,
    (congrFun hdenv v1).trans hbc.one, (congrFun hdenv v2).trans hbc.two⟩
  have hk : r.selected.1.k < r.call.n := (Cells.prepare_spec _ r.selected.1 r.selected.2).k_lt_n
  have hwlen : r.selected.1.k ≤ witness.length := by
    simp only [witness, Program.witnessPrefix, List.length_ofFn, Program.witnessReadLength]
    omega
  obtain ⟨e, n3, he3, hn3, hev, heram, heip, heout, _hestreams, hec⟩ :=
    StagePrint.Header.readTranslation_run C r.selected.1 witness d hdc hdparam hdwit hwlen
    (Nat.pow_lt_pow_right (by decide) (by omega)) (lt_trans (by omega) Nat.lt_two_pow_self)
  have hesource : EntrySourceData r e := by
    refine ⟨?_, heram ▸ hdparam, heram ▸ hdwit,
      he3.rc_le hcursor,
      hev.trans (entryPointRequest_translation r false false).symm⟩
    exact (congrFun heram callStore).trans ((hdother _ (by decide)).1.trans hbdata.originalCall)
  have heprepared : e.ram compactStore = (Program.prepWord B1 B2 r.call r.witness).map Bool.toNat := by
    rw [heram, (hdother _ (by decide)).1, hbram6, prepWord_eq_compact r.dispatched]
  have helengths : e.ram entryLengthStore =
      [(Program.prepWord B1 B2 r.call r.witness).length, (callWord r.call).length,
        (preparedPrefixWord r.call r.selected.1).length] := by
    rw [heram, hdlengths, hblen, hbdata.callBytes, hb41, prepWord_eq_compact r.dispatched]
  have hdo : d.out = b.out := congrArg (fun t => t.2.1) hdrest
  have hmo : m.out = a.out := congrArg (fun t => t.1) hmrest
  have hbo : b.out = m.out := congrArg (fun t => t.1) hbrest
  have hdi : d.ip = b.ip := congrArg (fun t => t.1) hdrest
  have hmstreams : (m.kin, m.kout, m.kc) = (a.kin, a.kout, a.kc) :=
    congrArg (fun t => (t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hmrest
  have hbstreams : (b.kin, b.kout, b.kc) = (m.kin, m.kout, m.kc) :=
    congrArg (fun t => (t.2.1, t.2.2.1, t.2.2.2)) hbrest
  have hdstreams : (d.kin, d.kout, d.kc) = (b.kin, b.kout, b.kc) :=
    congrArg (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2)) hdrest
  have ht : n3 ≤ 106 + StagePrint.Header.translationCost witness.length r.selected.1.k := by
    apply hn3.trans
    unfold StagePrint.Header.translationCost
    nlinarith
  unfold acquireSizedEntrySource
  refine ⟨e, n0 + (n1 + (n2 + n3 + 1) + 1) + 1,
    Ex.seq he0 (Ex.seq he1 (Ex.seq he2 he3)), ?_,
    ⟨hesource, heprepared, helengths⟩, ?_, heout.trans (hdo.trans (hbo.trans hmo)), hec,
    _hestreams.trans (hdstreams.trans (hbstreams.trans hmstreams))⟩
  · change n0 + (n1 + (n2 + n3 + 1) + 1) + 1 ≤
      3000 * ((callWord r.call).length + 1)^3 +
      4000 * ((Program.parametersWord r.selected.1).length + 1)^2 +
      5 * (preparedPrefixWord r.call r.selected.1).length + 30 +
      initializeCost r.call r.selected.1 witness prep.length +
      StagePrint.Header.translationCost witness.length r.selected.1.k + 114
    omega
  · rw [heip, hdi, hbip, hmip, prepWord_eq_compact r.dispatched]

end NearQuarticWires.StageMainMask
