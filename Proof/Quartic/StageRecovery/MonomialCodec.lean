import Proof.Quartic.StageRecovery.SupportCount
import Proof.Quartic.StageRecovery.SupportEmit
import Proof.Quartic.StageRecovery.CoefficientCodec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the canonical
monomial writer uses only its finite support and natural-codec work frame. -/
def monomialScratch : List (Fin VV) := supportCountScratch ++ supportEmitScratch

/-- `lem:print`, paper/paper.tex: one canonical term
is written by counting the actual support, printing that count, scanning
its indices in order, and printing the actual nonnegative coefficient. -/
def emitMonomialProgram : St VV MM :=
  .seq countSupportProgram
    (.seq (emitVariable supportDegree)
      (.seq emitSupportIndicesProgram emitCoefficientProgram))

/-- `prop:time`, paper/paper.tex: the actual support
and coefficient writer costs add and have only a fixed polynomial arity
and coefficient-bit factor. -/
def monomialCost (V c : ℕ) : ℕ :=
  (10 * V + 8) + ((40 * (V + 1) + 42) +
    ((V * (40 * (V + 1) + 54) + 6) +
      (40 * natBitLength 0 + 40 * natBitLength c + 85) + 1) + 1) + 1

/-- `lem:print`, paper/paper.tex: one actual support
and coefficient pair is serialized in the unchanged canonical Terms
format, preserving every input, record-store and call-stream head. -/
theorem emitMonomialProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V s c : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (hcoeff : a.env coefficientVar = c) (hW : 2 ≤ C.Wd)
    (hVfit : V + 3 < 2 ^ C.Wd)
    (hzero : natBitLength 0 + 2 < 2 ^ C.Wd)
    (hfit : natBitLength c + 2 < 2 ^ C.Wd) :
    Hs C emitMonomialProgram a (monomialCost V c) (fun b =>
      b.out = a.out ++ monoWord (setOf V s, (c : ℤ)) ∧
      supportPrintRest b = supportPrintRest a ∧ Cst b ∧ Fr a b monomialScratch) := by
  have hfour : 4 ≤ 2 ^ C.Wd :=
    (show 4 = 2 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by decide) hW)
  have hcard : (setOf V s).card ≤ V := by
    simpa using (Finset.card_le_univ (setOf V s))
  have hcardbits := nbl_le_self (setOf V s).card
  unfold emitMonomialProgram monomialCost
  refine Hs.seq (t2 := (40 * (V + 1) + 42) +
    ((V * (40 * (V + 1) + 54) + 6) +
      (40 * natBitLength 0 + 40 * natBitLength c + 85) + 1) + 1)
    (countSupportProgram_spec C a hc V s hV hs (by omega) hfour)
    fun b ⟨hbd, hbsh, hbc, hbf⟩ => ?_
  have hsame := Same.of_sh hbsh
  refine Hs.seq (t2 := (V * (40 * (V + 1) + 54) + 6) +
      (40 * natBitLength 0 + 40 * natBitLength c + 85) + 1)
    ((emitVariable_spec C b hbc supportDegree (by decide) hW (by rw [hbd]; omega)).mono
      (by rw [hbd]; omega) (fun _ h => h))
    fun d ⟨hdo, hdr, hdc, hdf⟩ => ?_
  have hdV : d.env arityVar = V := by rw [hdf _ (by decide), hbf _ (by decide), hV]
  have hds : d.env supportVar = s := by rw [hdf _ (by decide), hbf _ (by decide), hs]
  refine Hs.seq (t2 := 40 * natBitLength 0 + 40 * natBitLength c + 85)
    (emitSupportIndicesProgram_spec C d hdc V s hdV hds hVfit hW)
    fun e ⟨heo, her, hec, hef⟩ => ?_
  have hecoeff : e.env coefficientVar = c := by
    rw [hef _ (by decide), hdf _ (by decide), hbf _ (by decide), hcoeff]
  refine (emitCoefficientProgram_spec C e hec c hecoeff hW hzero hfit).mono le_rfl ?_
  rintro f ⟨hfo, hfr, hfc, hff⟩
  refine ⟨?_, hfr.trans (her.trans (hdr.trans ?_)), hfc,
    Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide))
        (Fr.trans (Fr.weaken hef (by decide)) (Fr.weaken hff (by decide))))⟩
  · rw [hfo, heo, hdo, hsame.out, hbd]
    simp only [monoWord, listWord, supportIndices_sorted, supportIndices_length,
      List.append_assoc]
  · simp only [supportPrintRest, hsame.ip, hsame.ram, hsame.rc, hsame.kin, hsame.kout, hsame.kc]

end NearQuarticWires.StageRecovery
