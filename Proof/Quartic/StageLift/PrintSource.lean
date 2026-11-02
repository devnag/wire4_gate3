import Proof.Quartic.StageLift.CallSource
import Proof.Quartic.StageLift.PrintSuffix

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain.CallSkip

/-- `lem:print` and Step 3, paper/paper.tex: the actual print source is read from its tagged call, not
from a decoded parameter, witness, Gamma or original-gate provider. -/
def readPrintSource : St VV MM := .seq readCallSource readPrintSuffix

/-- `lem:print` and Step 3, paper/paper.tex: the exact data retained by the complete physical source
reader, with one finite original call and one Gamma table. -/
structure PrintSourceData {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) : Prop where
  originalCall : a.ram callStore = (callWord r.child.call).map Bool.toNat
  scalarFields : a.ram parameterStore = parameterScalars r.child.selected.1
  primeFields : a.ram primeStore = r.child.selected.1.primes.sort (· ≤ ·)
  factorFields : a.ram factorStore = r.child.selected.1.factors
  witnessBits : a.ram witnessStore =
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).map Bool.toNat
  gammaBits : a.ram gammaStore =
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat
  callBytes : a.env lengthCounter = (callWord r.child.call).length
  primeCount : a.env primeCountVar = r.child.selected.1.primes.card
  factorCount : a.env factorCountVar = r.child.selected.1.factors.length
  scalarCursor : a.rc parameterStore = 46
  primeCursor : a.rc primeStore = r.child.selected.1.primes.card
  factorCursor : a.rc factorStore = r.child.selected.1.factors.length
  witnessCursor : a.rc witnessStore =
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length
  gammaCursor : a.rc gammaStore =
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length
  callCursor : a.rc callStore = (callWord r.child.call).length

/-- `lem:print` and Step 3, paper/paper.tex: starting from the literal Greedy printInput, the complete
paid source reader reaches the original index bytes and retains exactly
the data required by the original-pool and Formula producers. -/
theorem readPrintSource_framed_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (B : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Greedy.printInput r ++ rest)
    (hcall : (callWord r.child.call).length + 2 ≤ C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields r.child.selected.1 ++
      r.child.selected.1.primes.sort (· ≤ ·) ++ parameterTailFields r.child.selected.1 ++
      r.child.selected.1.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : r.child.selected.1.primes.card < 2 ^ C.Wd ∧
      r.child.selected.1.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore, gammaStore, callStore],
      a.ram store = [] ∧ a.rc store = 0) :
    Hs C readPrintSource a
      (3000 * ((callWord r.child.call).length + 1) ^ 3 + 12 * (callWord r.child.call).length +
        parameterReadCost r.child.selected.1 B +
        8 * (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length +
        8 * (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length + 27)
      (fun b => (PrintSourceData r b ∧ C.inp.drop b.ip = Greedy.printIndexWord r ++ rest ∧
        (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b) ∧
        (∀ other, other ∉ [parameterStore, primeStore, factorStore, witnessStore, gammaStore, callStore] →
          b.ram other = a.ram other ∧ b.rc other = a.rc other)) := by
  let p := r.child.selected.1
  let W := Program.witnessPrefix r.child.call p r.child.witness
  let G := listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)
  let tail := Program.parametersWord p ++ frame W ++ frame G ++ Greedy.printIndexWord r ++ rest
  have hinput : C.inp.drop a.ip = true :: (callWord r.child.call ++ tail) := by
    rw [hin, printInput_layout]
    simp only [tail, W, G, p, List.cons_append, List.append_assoc]
  unfold readPrintSource
  refine (Hs.seq
    (t1 := 3000 * ((callWord r.child.call).length + 1) ^ 3 + 12 * (callWord r.child.call).length + 16)
    (t2 := parameterReadCost p B + 8 * W.length + 8 * G.length + 10)
    (readCallSource_spec C r.child.call tail a hc hinput hcall (hempty _ (by simp)))
    fun b ⟨hbi, hbl, hbcall, _hbcallc, hbother, hbsh, hbc, _hbfr⟩ => ?_).mono
      (by dsimp only [p, W, G]; omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = Program.parametersWord p ++
      frame W ++ frame G ++ (Greedy.printIndexWord r ++ rest) := by
    rw [hbi, show a.ip + 1 + (callWord r.child.call).length =
      a.ip + ((callWord r.child.call).length + 1) by omega, ← List.drop_drop, hinput]
    simp only [List.drop_succ_cons, List.drop_left, tail, List.append_assoc]
  have hbempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore, gammaStore],
      b.ram store = [] ∧ b.rc store = 0 := by
    intro store hs
    have hne : store ≠ callStore := by
      rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hs) with
        hs | hs | hs | hs | hs <;> subst store <;> decide
    obtain ⟨hr, hrc⟩ := hbother store hne
    rw [hr, hrc]
    exact hempty store (by simp only [List.mem_cons] at hs ⊢; tauto)
  refine (readPrintSuffix_spec C p B W G (Greedy.printIndexWord r ++ rest) b hbc hbin
    hwidth hB hcounts hbempty).mono le_rfl ?_
  rintro d ⟨hdi, hdpar, hdprime, hdfactor, _hdpc, _hdprc, _hdfc, hdwit, hdgamma,
    _hdwc, _hdgc, hdpn, hdfn, hdother, hdsh, hdc, hdfr⟩
  refine ⟨?_, ?_⟩
  ·
    refine ⟨⟨?_, hdpar, hdprime, hdfactor, hdwit, hdgamma, ?_, hdpn, hdfn,
        _hdpc, _hdprc, _hdfc, _hdwc, _hdgc, ?_⟩,
      ?_, hdsh.trans hbsh, hdc⟩
    · rw [(hdother callStore (by decide)).1, hbcall]
    · rw [hdfr lengthCounter (by decide), hbl]
    · rw [(hdother callStore (by decide)).2, _hbcallc]
    · have hcombined : C.inp.drop b.ip =
          (Program.parametersWord p ++ frame W ++ frame G) ++ (Greedy.printIndexWord r ++ rest) := by
        simpa only [List.append_assoc] using hbin
      rw [hdi, show b.ip + (Program.parametersWord p).length + (frame W).length + (frame G).length =
          b.ip + (Program.parametersWord p ++ frame W ++ frame G).length by
            simp only [List.length_append]; omega,
        ← List.drop_drop, hcombined, List.drop_left]
  · intro other ho
    have hcall : other ≠ callStore := by intro h; exact ho (by simp [h])
    have hparams : other ∉ [parameterStore, primeStore, factorStore, witnessStore, gammaStore] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ho ⊢
      tauto
    obtain ⟨hr₁, hc₁⟩ := hdother other hparams
    obtain ⟨hr₂, hc₂⟩ := hbother other hcall
    exact ⟨hr₁.trans hr₂, hc₁.trans hc₂⟩

/-- `lem:print` and Step 3, paper/paper.tex: the original source-reader interface follows from the
stronger execution that also preserves every unrelated scratch store. -/
theorem readPrintSource_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (B : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Greedy.printInput r ++ rest)
    (hcall : (callWord r.child.call).length + 2 ≤ C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields r.child.selected.1 ++
      r.child.selected.1.primes.sort (· ≤ ·) ++ parameterTailFields r.child.selected.1 ++
      r.child.selected.1.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : r.child.selected.1.primes.card < 2 ^ C.Wd ∧
      r.child.selected.1.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore, gammaStore, callStore],
      a.ram store = [] ∧ a.rc store = 0) :
    Hs C readPrintSource a
      (3000 * ((callWord r.child.call).length + 1) ^ 3 + 12 * (callWord r.child.call).length +
        parameterReadCost r.child.selected.1 B +
        8 * (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length +
        8 * (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length + 27)
      (fun b => PrintSourceData r b ∧ C.inp.drop b.ip = Greedy.printIndexWord r ++ rest ∧
        (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  exact (readPrintSource_framed_spec C r B rest a hc hin hcall hwidth hB hcounts hempty).mono
    le_rfl (fun _ h => h.1)

end NearQuarticWires.StageLift
