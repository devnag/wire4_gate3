import Proof.Quartic.StageLift.PreparedReturn
import Proof.Quartic.StageLift.RegisterFrame

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `lem:print`, paper/paper.tex: the original finite preparation word carried once
to all source queries, before any Gamma payload or raw target suffix. -/
noncomputable def preparedWordOf {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  StageMain.Compact.compactInput r.child.call r.child.selected.1
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness)

/-- Step 3 and `lem:print`, paper/paper.tex: cache the small original source, return its head,
then run the complete actual source and unbounded-index decoder. -/
def readCachedPrintRequest : St VV MM := .seq cachePreparedInput readPrintRequest

/-- Step 3 and `lem:print`, paper/paper.tex: the source-acquisition clock charges the original
small-prefix pass, Gamma retention, and raw target processing once. -/
noncomputable def cachedRequestCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (B Bi R : ℕ) : ℕ :=
  StageMain.Compact.acquireCost r.child.call r.child.selected.1
      (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness) +
    5 * (preparedWordOf r).length + 10 + printSourceCost r B +
    7 * r.child.selected.1.e + 30 * natBitLength r.prime + indexTargetsCost r Bi R + 1047

/-- Step 3 and `lem:print`, paper/paper.tex: the complete literal printer input supplies every
retained source, the actual modulus and normalized indices, together
with one finite raw preparation cache and its physically measured length.
There is no source/provider word or precomputed prefix-length input. -/
theorem readCachedPrintRequest_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (B Bi : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Greedy.printInput r ++ rest)
    (hprepared : (preparedPrefixWord r.child.call r.child.selected.1).length + 2 ≤ C.Wd)
    (hP : (preparedWordOf r).length < 2 ^ C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields r.child.selected.1 ++
      r.child.selected.1.primes.sort (· ≤ ·) ++ parameterTailFields r.child.selected.1 ++
      r.child.selected.1.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : r.child.selected.1.primes.card < 2 ^ C.Wd ∧
      r.child.selected.1.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore,
      gammaStore, callStore, indexStore, preparedStore], a.ram store = [] ∧ a.rc store = 0)
    (hW : 6 ≤ C.Wd) (hprime : natBitLength r.prime + 2 ≤ C.Wd)
    (hfit : 2 * r.prime ^ r.child.selected.1.e ≤ 2 ^ C.Wd)
    (hbits : ∀ z ∈ printDigitList r ++ printResidueList r, natBitLength z.natAbs ≤ Bi)
    (hcountWidths : natBitLength (printDigitList r).length + 2 ≤ C.Wd ∧
      natBitLength (printResidueList r).length + 2 ≤ C.Wd)
    (hcountFits : (printDigitList r).length < 2 ^ C.Wd ∧
      (printResidueList r).length < 2 ^ C.Wd) :
    Hs C readCachedPrintRequest a (cachedRequestCost r B Bi (a.rc indexMarkerStore)) (fun b =>
      PrintRequestData r b ∧ b.ram preparedStore = (preparedWordOf r).map Bool.toNat ∧
      b.env preparedLength = (preparedWordOf r).length ∧ b.rc preparedStore = (preparedWordOf r).length ∧
      C.inp.drop b.ip = rest ∧ b.rc indexMarkerStore ≤ a.rc indexMarkerStore + 2 * Bi + 2 ∧
      (∀ store, store ∉ [parameterStore, primeStore, factorStore, witnessStore,
        gammaStore, callStore, indexStore, indexMarkerStore, preparedStore] →
        b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  let W := Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness
  let tail := Greedy.gammaTableWord r.child ++ Greedy.printIndexWord r ++ rest
  have hinput : C.inp.drop a.ip = preparedWordOf r ++ tail := by
    rw [hin, printInput_preparedPrefix]
    simp only [preparedWordOf, StageMain.Compact.compactInput, tail, List.append_assoc]
  have hcache := cachePreparedInput_spec C r.child.call r.child.selected.1 W tail a hc
    hinput hprepared hP (hempty preparedStore (by simp))
  have hcall : (callWord r.child.call).length + 2 ≤ C.Wd := by
    simp only [preparedPrefixWord, List.length_cons, List.length_append] at hprepared
    omega
  unfold readCachedPrintRequest
  refine (Hs.seq
    (t1 := StageMain.Compact.acquireCost r.child.call r.child.selected.1 W +
      5 * (preparedWordOf r).length + 9)
    (t2 := printSourceCost r B + 7 * r.child.selected.1.e + 30 * natBitLength r.prime +
      indexTargetsCost r Bi (a.rc indexMarkerStore) + 1047) hcache
    fun b ⟨hbi, hbl, hbram, hbrc, hbo, hbsh, hbc, _hbfr⟩ => ?_).mono
      (by unfold cachedRequestCost; dsimp only [W]; omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = Greedy.printInput r ++ rest := by rw [hbi]; exact hin
  have hbempty : ∀ store ∈ [parameterStore, primeStore, factorStore, witnessStore, gammaStore, callStore],
      b.ram store = [] ∧ b.rc store = 0 := by
    intro store hs
    have hne : store ≠ preparedStore := by
      rcases (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hs) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [(hbo store hne).1, (hbo store hne).2]
    exact hempty store (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢; tauto)
  have hbindex : b.ram indexStore = [] ∧ b.rc indexStore = 0 := by
    rw [(hbo indexStore (by decide)).1, (hbo indexStore (by decide)).2]
    exact hempty indexStore (by simp)
  have hs := readPrintRequest_spec C r B Bi rest b hbc hbin hcall hwidth hB hcounts hbempty
    hbindex hW hprime hfit hbits hcountWidths hcountFits
  rw [(hbo indexMarkerStore (by decide)).2] at hs
  obtain ⟨d, n, he, hn, hddata, hdinput, hdmarker, hdo, hdsh, hdc⟩ := hs
  refine ⟨d, n, he, hn, hddata, ?_, ?_, ?_, hdinput, hdmarker, ?_, hdsh.trans hbsh, hdc⟩
  · rw [(hdo preparedStore (by decide)).1]
    exact hbram
  · exact (readPrintRequest_preserves_preparedLength he).trans hbl
  · rw [(hdo preparedStore (by decide)).2]
    exact hbrc
  · intro store hs'
    have hp : store ≠ preparedStore := by intro h; exact hs' (by simp [h])
    have ho : store ∉ [parameterStore, primeStore, factorStore, witnessStore,
        gammaStore, callStore, indexStore, indexMarkerStore] := by
      intro h
      exact hs' (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    obtain ⟨hr, hc'⟩ := hdo store ho
    obtain ⟨hr', hc''⟩ := hbo store hp
    exact ⟨hr.trans hr', hc'.trans hc''⟩

end NearQuarticWires.StageLift
