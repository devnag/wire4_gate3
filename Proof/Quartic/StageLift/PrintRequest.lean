import Proof.Quartic.StageLift.PrintSource
import Proof.Quartic.StageLift.PrintIndex

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain.CallSkip NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: acquisition of
the original source is followed by the complete bounded-residue index pass. -/
def readPrintRequest : St VV MM := .seq readPrintSource readPrintIndex

/-- `lem:print` and Step 3, paper/paper.tex: the once-paid physical acquisition of the retained source. -/
noncomputable def printSourceCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (B : ℕ) : ℕ :=
  3000 * ((callWord r.child.call).length + 1) ^ 3 + 12 * (callWord r.child.call).length +
    parameterReadCost r.child.selected.1 B +
    8 * (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length +
    8 * (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length + 27

/-- `lem:print`, paper/paper.tex: bounded index
records retain the literal side, sign pattern and actual prime before
the circuit-major digit list and the two score targets. -/
noncomputable def normalizedPrintIndex {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List ℕ :=
  [r.sign.toNat] ++ (List.ofFn r.pattern).map Bool.toNat ++ [r.prime] ++
    (printDigitList r ++ printResidueList r).map
      (fun z : ℤ => (z % (r.prime ^ r.child.selected.1.e : ℤ)).toNat)

/-- `lem:print` and Step 3, paper/paper.tex: the source and normalized indices actually retained after
consuming the complete original printer input. -/
structure PrintRequestData {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) : Prop where
  originalCall : a.ram callStore = (callWord r.child.call).map Bool.toNat
  scalarFields : a.ram parameterStore = parameterScalars r.child.selected.1
  primeFields : a.ram primeStore = r.child.selected.1.primes.sort (· ≤ ·)
  factorFields : a.ram factorStore = r.child.selected.1.factors
  witnessBits : a.ram witnessStore =
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).map Bool.toNat
  gammaBits : a.ram gammaStore =
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat
  indexFields : a.ram indexStore = normalizedPrintIndex r
  modulus : a.env modulusVar = r.prime ^ r.child.selected.1.e
  prime : a.env indexPrimeVar = r.prime
  callBytes : a.env lengthCounter = (callWord r.child.call).length
  primeCount : a.env primeCountVar = r.child.selected.1.primes.card
  factorCount : a.env factorCountVar = r.child.selected.1.factors.length
  scalarCursor : a.rc parameterStore = 27
  primeCursor : a.rc primeStore = r.child.selected.1.primes.card
  factorCursor : a.rc factorStore = r.child.selected.1.factors.length
  witnessCursor : a.rc witnessStore =
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length
  gammaCursor : a.rc gammaStore =
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length
  callCursor : a.rc callStore = (callWord r.child.call).length
  indexCursor : a.rc indexStore = 10 + (printDigitList r).length + (printResidueList r).length

/-- `lem:print` and Step 3, paper/paper.tex: the complete literal printInput supplies the original
call, actual parameters, witness, Gamma table and normalized index bank.
Raw target bit lengths occur only in the paid processing cost. -/
theorem readPrintRequest_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (B Bi : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Greedy.printInput r ++ rest)
    (hcall : (callWord r.child.call).length + 2 ≤ C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields r.child.selected.1 ++
      r.child.selected.1.primes.sort (· ≤ ·) ++ parameterTailFields r.child.selected.1 ++
      r.child.selected.1.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : r.child.selected.1.primes.card < 2 ^ C.Wd ∧
      r.child.selected.1.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore, gammaStore, callStore],
      a.ram store = [] ∧ a.rc store = 0)
    (hindex : a.ram indexStore = [] ∧ a.rc indexStore = 0)
    (hW : 6 ≤ C.Wd) (hprime : natBitLength r.prime + 2 ≤ C.Wd)
    (hfit : 2 * r.prime ^ r.child.selected.1.e ≤ 2 ^ C.Wd)
    (hbits : ∀ z ∈ printDigitList r ++ printResidueList r, natBitLength z.natAbs ≤ Bi)
    (hcountWidths : natBitLength (printDigitList r).length + 2 ≤ C.Wd ∧
      natBitLength (printResidueList r).length + 2 ≤ C.Wd)
    (hcountFits : (printDigitList r).length < 2 ^ C.Wd ∧
      (printResidueList r).length < 2 ^ C.Wd) :
    Hs C readPrintRequest a
      (printSourceCost r B + 7 * r.child.selected.1.e + 30 * natBitLength r.prime +
        indexTargetsCost r Bi (a.rc indexMarkerStore) + 1047) (fun b =>
      PrintRequestData r b ∧ C.inp.drop b.ip = rest ∧
      b.rc indexMarkerStore ≤ a.rc indexMarkerStore + 2 * Bi + 2 ∧
      (∀ other, other ∉ [parameterStore, primeStore, factorStore, witnessStore,
        gammaStore, callStore, indexStore, indexMarkerStore] →
        b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  have hs := readPrintSource_framed_spec C r B rest a hc hin hcall hwidth hB hcounts hempty
  change Hs C readPrintSource a (printSourceCost r B) _ at hs
  unfold readPrintRequest
  refine (Hs.seq (t1 := printSourceCost r B)
    (t2 := 46 + 7 * r.child.selected.1.e + 30 * natBitLength r.prime +
      indexTargetsCost r Bi (a.rc indexMarkerStore) + 1000) hs
    fun b ⟨⟨hb, hbin, hbsh, hbc⟩, hbo⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbank := hbo indexStore (by decide)
  have hmarker := hbo indexMarkerStore (by decide)
  have hbindex : b.rc indexStore = (b.ram indexStore).length := by
    rw [hbank.1, hbank.2, hindex.1, hindex.2]
    rfl
  have hi := readPrintIndex_spec C r Bi rest b hbc hbin hb.scalarFields hbindex hW hprime
    hfit hbits hcountWidths hcountFits
  rw [hb.scalarCursor, hmarker.2] at hi
  refine hi.mono le_rfl ?_
  rintro d ⟨hdq, hdp, hdbank, hdindex, hdmarker, hdscalar, hdi, hdram, hdrc, hdsh, hdc, hdf⟩
  have hram (store : Fin MM) (h₁ : store ≠ indexStore) (h₂ : store ≠ indexMarkerStore) :
      d.ram store = b.ram store := hdram store h₁ h₂
  have hrc (store : Fin MM) (h₁ : store ≠ indexStore) (h₂ : store ≠ indexMarkerStore)
      (h₃ : store ≠ parameterStore) : d.rc store = b.rc store := hdrc store h₁ h₂ h₃
  refine ⟨?_, ?_, hdmarker, ?_, hdsh.trans hbsh, hdc⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hdq, hdp, ?_, ?_, ?_, hdscalar,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hram _ (by decide) (by decide)).trans hb.originalCall
    · exact (hram _ (by decide) (by decide)).trans hb.scalarFields
    · exact (hram _ (by decide) (by decide)).trans hb.primeFields
    · exact (hram _ (by decide) (by decide)).trans hb.factorFields
    · exact (hram _ (by decide) (by decide)).trans hb.witnessBits
    · exact (hram _ (by decide) (by decide)).trans hb.gammaBits
    · simpa only [hbank.1, hindex.1, List.nil_append, normalizedPrintIndex] using hdbank
    · exact (hdf lengthCounter (by decide)).trans hb.callBytes
    · exact (hdf primeCountVar (by decide)).trans hb.primeCount
    · exact (hdf factorCountVar (by decide)).trans hb.factorCount
    · exact (hrc _ (by decide) (by decide) (by decide)).trans hb.primeCursor
    · exact (hrc _ (by decide) (by decide) (by decide)).trans hb.factorCursor
    · exact (hrc _ (by decide) (by decide) (by decide)).trans hb.witnessCursor
    · exact (hrc _ (by decide) (by decide) (by decide)).trans hb.gammaCursor
    · exact (hrc _ (by decide) (by decide) (by decide)).trans hb.callCursor
    · simpa only [hbank.2, hindex.2, zero_add] using hdindex
  · rw [hdi, ← List.drop_drop, hbin, List.drop_left]
  · intro other ho
    have hi : other ≠ indexStore := by intro h; exact ho (by simp [h])
    have hm : other ≠ indexMarkerStore := by intro h; exact ho (by simp [h])
    have hp : other ≠ parameterStore := by intro h; exact ho (by simp [h])
    have hs : other ∉ [parameterStore, primeStore, factorStore, witnessStore, gammaStore, callStore] := by
      intro h
      exact ho (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    exact ⟨(hram other hi hm).trans (hbo other hs).1,
      (hrc other hi hm hp).trans (hbo other hs).2⟩

end NearQuarticWires.StageLift
