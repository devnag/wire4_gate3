import Proof.Quartic.StageLift.IndexHeader
import Proof.Quartic.StageLift.IndexTargets
import Proof.Quartic.Reconstruct.Gather

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: the complete
actual index reader computes q before streaming either original signed
target list, and retains only bounded residues for the per-walk producer. -/
def readPrintIndex : St VV MM :=
  .seq readPrintIndexHeader (.seq computeIndexModulus
    (readIndexTargets indexMarkerStore indexStore indexCountVar))

/-- `lem:print`, paper/paper.tex: the complete
index reader preserves every register outside its literal source,
binary arithmetic, marker-replay and counted-list workspace. -/
def indexScratch : List (Fin VV) :=
  indexPrimeVar :: indexExponentVar :: modulusVar :: a1 :: c4 ::
    indexCountVar :: fieldIndex :: signedStreamScratch

/-- `lem:print`, paper/paper.tex: the raw-index
processing term is paid once from the actual lengths of its two lists
and their encoded signed magnitudes. -/
noncomputable def indexTargetsCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (B R : ℕ) : ℕ :=
  ((printDigitList r).length + (printResidueList r).length) * (R + 32 * B + 128) +
    30 * (natBitLength (printDigitList r).length + natBitLength (printResidueList r).length) + 75

/-- `lem:print` and `lem:residue`, paper/paper.tex: the literal complete index word supplies its actual
prime, q=p^e and normalized digit/score record bank. Arbitrarily large
raw signed values affect only the once-paid input-processing term. -/
theorem readPrintIndex_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (B : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Greedy.printIndexWord r ++ rest)
    (hparams : a.ram parameterStore = parameterScalars r.child.selected.1)
    (hcursor : a.rc indexStore = (a.ram indexStore).length)
    (hW : 6 ≤ C.Wd) (hprime : natBitLength r.prime + 2 ≤ C.Wd)
    (hfit : 2 * r.prime ^ r.child.selected.1.e ≤ 2 ^ C.Wd)
    (hbits : ∀ z ∈ printDigitList r ++ printResidueList r, natBitLength z.natAbs ≤ B)
    (hcountWidths : natBitLength (printDigitList r).length + 2 ≤ C.Wd ∧
      natBitLength (printResidueList r).length + 2 ≤ C.Wd)
    (hcountFits : (printDigitList r).length < 2 ^ C.Wd ∧
      (printResidueList r).length < 2 ^ C.Wd) :
    Hs C readPrintIndex a
      (a.rc parameterStore + 7 * r.child.selected.1.e + 30 * natBitLength r.prime +
        indexTargetsCost r B (a.rc indexMarkerStore) + 1000) (fun b =>
      b.env modulusVar = r.prime ^ r.child.selected.1.e ∧ b.env indexPrimeVar = r.prime ∧
      b.ram indexStore = a.ram indexStore ++
        ([r.sign.toNat] ++ (List.ofFn r.pattern).map Bool.toNat ++ [r.prime] ++
          (printDigitList r ++ printResidueList r).map
            (fun z : ℤ => (z % (r.prime ^ r.child.selected.1.e : ℤ)).toNat)) ∧
      b.rc indexStore = a.rc indexStore + 10 + (printDigitList r).length + (printResidueList r).length ∧
      b.rc indexMarkerStore ≤ a.rc indexMarkerStore + 2 * B + 2 ∧ b.rc parameterStore = 27 ∧
      b.ip = a.ip + (Greedy.printIndexWord r).length ∧
      (∀ other, other ≠ indexStore → other ≠ indexMarkerStore → b.ram other = a.ram other) ∧
      (∀ other, other ≠ indexStore → other ≠ indexMarkerStore → other ≠ parameterStore →
        b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b indexScratch) := by
  let p := r.child.selected.1
  let q := r.prime ^ p.e
  let digits := printDigitList r
  let residues := printResidueList r
  have hp : 2 ≤ r.prime := (Reconstruct.PrintRequest.prime_prime r).two_le
  have hq : 2 ≤ q := Reconstruct.PrintRequest.two_le_modulus r
  have hinput : C.inp.drop a.ip = printIndexHeader r ++
      (listWord NearCubicGates.Close.Interfaces.intWord digits ++
        listWord NearCubicGates.Close.Interfaces.intWord residues ++ rest) := by
    rw [hin, printIndexWord_layout]
    simp only [digits, residues, List.append_assoc]
  unfold readPrintIndex
  refine (Hs.seq (t1 := 30 * natBitLength r.prime + 900)
    (t2 := a.rc parameterStore + 7 * p.e + 67 + indexTargetsCost r B (a.rc indexMarkerStore))
    (readPrintIndexHeader_spec C r _ a hc hinput hW hprime hcursor)
    fun b ⟨hbp, hbr, hbrc, hbi, hbo, hbsh, hbc, hbf⟩ => ?_).mono
      (by dsimp only [p]; omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = listWord NearCubicGates.Close.Interfaces.intWord digits ++
      listWord NearCubicGates.Close.Interfaces.intWord residues ++ rest := by
    rw [hbi, ← List.drop_drop, hinput, List.drop_left]
  have hbparams : b.ram parameterStore = parameterScalars p := by
    rw [(hbo parameterStore (by decide)).1]
    exact hparams
  have hbcursor0 : b.rc parameterStore = a.rc parameterStore := (hbo _ (by decide)).2
  have hbmarkers : b.rc indexMarkerStore = a.rc indexMarkerStore := (hbo _ (by decide)).2
  have hbcursor : b.rc indexStore = (b.ram indexStore).length := by
    rw [hbr, hbrc]
    simp only [List.length_append, List.length_singleton, print_pattern_length]
    omega
  have hmod := computeIndexModulus_framed_spec C p r.prime b hbc hbparams hbp hp hfit
  rw [hbcursor0] at hmod
  refine (Hs.seq (t1 := a.rc parameterStore + 7 * p.e + 66)
    (t2 := indexTargetsCost r B (a.rc indexMarkerStore)) hmod
    fun c ⟨⟨hcq, _hce, hcp, hccursor0, hcram, hcsh, hcc, hcf⟩, hcrc⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hcip : c.ip = b.ip := congrArg (fun t => t.1) hcsh
  have hcsmall : (c.out, c.kin, c.kout, c.kc) = (b.out, b.kin, b.kout, b.kc) :=
    congrArg (fun t => (t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2)) hcsh
  have hcindex : c.rc indexStore = b.rc indexStore := by rw [hcrc, Function.update_of_ne (by decide)]
  have hcmarkers : c.rc indexMarkerStore = a.rc indexMarkerStore := by
    rw [hcrc, Function.update_of_ne (by decide), hbmarkers]
  have hcin : C.inp.drop c.ip = listWord NearCubicGates.Close.Interfaces.intWord digits ++
      listWord NearCubicGates.Close.Interfaces.intWord residues ++ rest := by
    rw [hcip]
    exact hbin
  have ht := readIndexTargets_spec C indexMarkerStore indexStore (by decide) indexCountVar
    (by decide) (by decide) (by decide) digits residues B q rest c hcc hcin hbits hq hcq hfit
    (by omega) hcountWidths hcountFits (by rw [hcindex, hcram]; exact hbcursor)
  rw [hcmarkers] at ht
  refine ht.mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdmc, hdo, hdsh, hdc, hdf⟩
  refine ⟨?_, ?_, ?_, ?_, hdmc, ?_, ?_, ?_, ?_, hdsh.trans (hcsmall.trans hbsh), hdc, ?_⟩
  · rw [hdf modulusVar (by decide)]
    exact hcq
  · rw [hdf indexPrimeVar (by decide)]
    exact hcp
  · rw [hdr, hcram, hbr]
    simp only [List.append_assoc, digits, residues, q, p, Nat.cast_pow]
  · rw [hdrc, hcindex, hbrc]
  · rw [(hdo parameterStore (by decide) (by decide)).2, hccursor0]
  · rw [hdi, hcip, hbi, printIndexWord_layout]
    simp only [List.length_append, digits, residues]
    omega
  · intro other hi hm
    rw [(hdo other hm hi).1, hcram, (hbo other hi).1]
  · intro other hi hm hp'
    rw [(hdo other hm hi).2, hcrc, Function.update_of_ne hp', (hbo other hi).2]
  · exact (hbf.weaken (by intro x hx; simp only [indexScratch, signedStreamScratch,
      List.mem_cons, List.mem_append] at hx ⊢; tauto)).trans
      ((hcf.weaken (by intro x hx; simp only [indexScratch, signedStreamScratch, rdNatT, List.mem_cons,
        List.mem_append] at hx ⊢; tauto)).trans
        (hdf.weaken (by intro x hx; simp only [indexScratch, List.mem_cons] at hx ⊢; tauto)))

end NearQuarticWires.StageLift
