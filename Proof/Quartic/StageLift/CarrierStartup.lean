import Proof.Quartic.StageLift.SourceAcquisition
import Proof.Quartic.StageLift.CarrierPrefix
import Proof.Quartic.StageLift.GammaStep
import Proof.Quartic.StagePrint.SourceValidity

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `prop:time`, paper/paper.tex: the startup clock uses only actual retained cursor
positions and the literal binary metadata fields. -/
noncomputable def carrierMetadataCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  27 + (10 + (printDigitList r).length + (printResidueList r).length) +
    (callWord r.child.call).length +
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length +
    30 * natBitLength r.child.call.n + 30 * natBitLength (kindTag r.child.call.kind) +
    30 * natBitLength (r.child.cellCall.seed.N ^ 8) + 1918

/-- Step 3 and `prop:time`, paper/paper.tex: source acquisition, actual metadata and the one-copy
carrier prefix all contribute their physical costs. -/
noncomputable def carrierStartupCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  sourceAcquisitionCost r 0 + carrierMetadataCost r + 9 * (preparedWordOf r).length +
    40 * (natBitLength (preparedWordOf r).length + natBitLength (r.child.cellCall.seed.N ^ 8)) + 96

/-- Step 3 and `lem:print`, paper/paper.tex: one real source acquisition initializes every walk
controller field, then physically emits the single preparation carrier. -/
def initializeCarrierSource : St VV MM :=
  .seq readCachedPrintRequest (.seq initializePrintMetadata emitCarrierPrefix)

/-- Step 3 and `lem:print`, paper/paper.tex: retained original source bytes and computed runtime
metadata at the first literal all-walk iteration. -/
structure CarrierStartData {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) : Prop where
  originalCall : a.ram callStore = (callWord r.child.call).map Bool.toNat
  scalarFields : a.ram parameterStore = parameterScalars r.child.selected.1
  primeFields : a.ram primeStore = r.child.selected.1.primes.sort (· ≤ ·)
  factorFields : a.ram factorStore = r.child.selected.1.factors
  witnessBits : a.ram witnessStore =
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).map Bool.toNat
  gammaBits : a.ram gammaStore =
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat
  indexFields : a.ram indexStore = normalizedPrintIndex r
  preparedBits : a.ram preparedStore = (preparedWordOf r).map Bool.toNat
  preparedBytes : a.env preparedLength = (preparedWordOf r).length
  degree : a.env degreeVar = residueDegreeBound r.child.selected.1 r.prime
  arity : a.env printArityVar = 17 * (Builder.allGates r.child.call).length
  exponent : a.env degreeExponent = r.child.selected.1.e
  chains : a.env degreeChain = r.child.selected.1.J
  modulus : a.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e
  prime : a.env degreePrime = r.prime
  signs : a.env signCodeVar = printPatternCode r.pattern
  kind : a.env callKindVar = kindTag r.child.call.kind
  walkIndex : a.env printWalkIndex = 0
  walkCount : a.env printWalkCount = r.child.cellCall.seed.N ^ 8
  gammaCursor : a.rc gammaStore = gammaByteCursor r 0
  preparedCursor : a.rc preparedStore = (preparedWordOf r).length

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: literal printInput alone produces
the exact frozen one-copy carrier prefix and every actual source field.
All numerical preconditions follow from the selected header allocation;
there is no additional runtime metadata, Formula or source-provider word. -/
theorem initializeCarrierSource_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (rest : List Bool) (a : DS VV MM)
    (hc : Cst a) (hv : Valid C a)
    (hin : C.inp.drop a.ip = Greedy.printInput r ++ rest)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C initializeCarrierSource a (carrierStartupCost r) (fun z =>
      z.out = a.out ++ natWord (preparedWordOf r).length ++ preparedWordOf r ++
        natWord (r.child.cellCall.seed.N ^ 8) ∧
      CarrierStartData r z ∧ C.inp.drop z.ip = rest ∧
      (z.kin, z.kout, z.kc) = (a.kin, a.kout, a.kc) ∧ Cst z ∧ Valid C z) := by
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hs := acquireSelectedPrintSource_spec C r rest a hc hin hW (fun store _ => hempty store)
  rw [(hempty indexMarkerStore).2] at hs
  obtain ⟨b, nb, heb, hnb, hbdata, hbram, hbP, hbrc, hbin, _hbmarker, hbother, hbsh, hbc⟩ := hs
  have hbempty : b.ram patternStore = [] ∧ b.rc patternStore = 0 := by
    rw [(hbother patternStore (by decide)).1, (hbother patternStore (by decide)).2]
    exact hempty patternStore
  have hm := initializePrintMetadata_selected_source_spec C r b hbc hbdata hbempty hW
  rw [hbdata.scalarCursor, hbdata.indexCursor, hbdata.callCursor, hbdata.gammaCursor] at hm
  change Hs C initializePrintMetadata b (carrierMetadataCost r) _ at hm
  obtain ⟨d, nd, hed, hnd, hdD, hdV, hde, hdJ, hdp, hdS, hdK, hdI, hdN, hdq, hdP,
    hdram, hdGamma, hdsh, hdc⟩ := hm
  have hdprep : d.ram preparedStore = (preparedWordOf r).map Bool.toNat :=
    (hdram _ (by decide)).trans hbram
  have hdPlen : d.env preparedLength = (preparedWordOf r).length := hdP.trans hbP
  have hdpc : d.rc preparedStore = (preparedWordOf r).length :=
    ((avoidsStore_spec hed (by decide)).2).trans hbrc
  have hPbound : (preparedWordOf r).length ≤ sourceEnvelope r := by dsimp [sourceEnvelope]; omega
  have hPbits := nbl_le_self (preparedWordOf r).length
  have hNbits := source_walk_counter_bits r
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hp := emitCarrierPrefix_spec C (preparedWordOf r) (r.child.cellCall.seed.N ^ 8) d hdc
    hdprep hdPlen hdN (by omega) (by omega) (by omega) (by omega)
  rw [hdpc] at hp
  obtain ⟨z, nz, hez, hnz, hzo, hzrc, hzsh, hzc, hzfr⟩ := hp
  have hzram : z.ram = d.ram := congrArg (fun t => t.2.1) hzsh
  have hzip : z.ip = d.ip := congrArg (fun t => t.1) hzsh
  have hdip : d.ip = b.ip := congrArg (fun t => t.1) hdsh
  have hdo : d.out = b.out := congrArg (fun t => t.2.1) hdsh
  have hbo : b.out = a.out := congrArg (fun t => t.1) hbsh
  have hcallee : (z.kin, z.kout, z.kc) = (a.kin, a.kout, a.kc) :=
    (congrArg (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2)) hzsh).trans
      ((congrArg (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2)) hdsh).trans
        (congrArg (fun t => (t.2.1, t.2.2.1, t.2.2.2)) hbsh))
  have hzmemory (store : Fin MM) (hne : store ≠ patternStore) : z.ram store = b.ram store := by
    rw [hzram]
    exact hdram store hne
  have hex : Ex C initializeCarrierSource a z (nb + (nd + nz + 1) + 1) :=
    Ex.seq heb (Ex.seq hed hez)
  have hvalid : Valid C z := hex.valid (by omega) (fun word _ =>
    (wf_out_len C.K.wf word).trans (by omega)) hv
  refine ⟨z, _, hex, ?_, ?_, ?_, ?_, hcallee, hzc, hvalid⟩
  · unfold carrierStartupCost
    omega
  · rw [hzo, hdo, hbo]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (hzfr _ (by decide)).trans hdD, (hzfr _ (by decide)).trans hdV,
      (hzfr _ (by decide)).trans hde, (hzfr _ (by decide)).trans hdJ,
      (hzfr _ (by decide)).trans hdq, (hzfr _ (by decide)).trans hdp,
      (hzfr _ (by decide)).trans hdS, (hzfr _ (by decide)).trans hdK,
      (hzfr _ (by decide)).trans hdI, (hzfr _ (by decide)).trans hdN, ?_, ?_⟩
    · exact (hzmemory _ (by decide)).trans hbdata.originalCall
    · exact (hzmemory _ (by decide)).trans hbdata.scalarFields
    · exact (hzmemory _ (by decide)).trans hbdata.primeFields
    · exact (hzmemory _ (by decide)).trans hbdata.factorFields
    · exact (hzmemory _ (by decide)).trans hbdata.witnessBits
    · exact (hzmemory _ (by decide)).trans hbdata.gammaBits
    · exact (hzmemory _ (by decide)).trans hbdata.indexFields
    · rw [hzram]
      exact hdprep
    · exact (hzfr _ (by decide)).trans hdPlen
    · rw [hzrc, Function.update_of_ne (by decide), gammaByteCursor_zero]
      exact hdGamma
    · rw [hzrc, Function.update_self]
  · rw [hzip, hdip]
    exact hbin

end NearQuarticWires.StageLift
