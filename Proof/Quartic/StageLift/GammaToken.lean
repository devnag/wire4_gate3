import Proof.Quartic.StageLift.GammaRead
import Proof.Quartic.StageLift.Token
import Proof.Quartic.StageLift.FormulaBytes
import Proof.Quartic.StageLift.PrintFrames

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats

/-- Step 3 and `lem:print`, paper/paper.tex: the literal split coefficient is immediately serialized as
the leading constant of the original walk's Formula source. -/
def emitGammaWeight : St VV MM :=
  .seq (readSplitGamma gammaStore) (emitNaturalConstant splitCoefficientVar)

/-- Step 3 and `lem:print`, paper/paper.tex: the real Gamma-field and token-printer workspace. -/
def gammaTokenScratch : List (Fin VV) :=
  splitCoefficientVar :: gammaSignVar :: gammaMagnitudeVar :: (rdNatT ++ tokenScratch)

/-- Step 3 and `lem:print`, paper/paper.tex: no split-weight word is supplied. The actual integer field
is read, split by the actual requested side, and emitted in the canonical
postfix constant codec, with the complete binary and rewind cost paid. -/
theorem emitGammaWeight_spec (C : Ctx) (bits : List Bool) (a : DS VV MM)
    (hc : Cst a) (ha : a.ram gammaStore = bits.map Bool.toNat)
    (side : Bool) (hpart : a.env partVar = side.toNat) (z : ℤ) (rest : List Bool)
    (hin : bits.drop (a.rc gammaStore) = NearCubicGates.Close.Interfaces.intWord z ++ rest)
    (hwidth : natBitLength z.natAbs + 2 ≤ C.Wd) (hW : 3 ≤ C.Wd) :
    Hs C emitGammaWeight a (70 * natBitLength z.natAbs + 155) (fun b =>
      b.out = a.out ++ tokWord (.const (splitMagnitude side z : ℤ)) ∧
      b.env splitCoefficientVar = splitMagnitude side z ∧
      b.rc gammaStore = a.rc gammaStore + (NearCubicGates.Close.Interfaces.intWord z).length ∧
      (b.ip, b.ram, Function.update b.rc gammaStore 0, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, Function.update a.rc gammaStore 0, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b gammaTokenScratch) := by
  have hsplit : splitMagnitude side z ≤ z.natAbs := by
    unfold splitMagnitude
    split <;> omega
  have hbit := codec_nbl_mono hsplit
  unfold emitGammaWeight
  refine (Hs.seq (t1 := 30 * natBitLength z.natAbs + 98)
    (t2 := 40 * natBitLength z.natAbs + 56)
    (readSplitGamma_spec C gammaStore bits a hc ha side hpart z rest hin hwidth hW)
    fun b ⟨hbv, hbcursor, hbrest, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbo : b.out = a.out := congrArg (fun t => t.2.1) hbrest
  have hfit : natBitLength (b.env splitCoefficientVar) + 2 < 2 ^ C.Wd := by
    rw [hbv]
    exact (show natBitLength (splitMagnitude side z) + 2 ≤ C.Wd by omega).trans_lt
      (Nat.lt_two_pow_self (n := C.Wd))
  refine (emitNaturalConstant_spec C splitCoefficientVar (by decide) (by decide)
    b hbc (by omega) hfit).mono (by rw [hbv]; omega) ?_
  rintro d ⟨hdo, hdrest, hdc, hdf⟩
  have hframes : Fr a d gammaTokenScratch :=
    (hbf.weaken (by
      intro x hx
      simp only [gammaTokenScratch, List.mem_cons, List.mem_append] at hx ⊢
      tauto)).trans (hdf.weaken (by
        intro x hx
        simp only [gammaTokenScratch, List.mem_cons, List.mem_append] at hx ⊢
        tauto))
  have hrc : d.rc = b.rc := congrArg (fun t => t.2.2.1) hdrest
  refine ⟨?_, ?_, by rw [hrc]; exact hbcursor, ?_, hdc, hframes⟩
  · rw [hdo, hbo, hbv]
  · rw [hdf splitCoefficientVar (by decide)]
    exact hbv
  · have hs : (d.ip, d.ram, Function.update d.rc gammaStore 0, d.kin, d.kout, d.kc) =
        (b.ip, b.ram, Function.update b.rc gammaStore 0, b.kin, b.kout, b.kc) :=
      congrArg (fun t => (t.1, t.2.1, Function.update t.2.2.1 gammaStore 0,
        t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdrest
    exact hs.trans (congrArg (fun t => (t.1, t.2.2.1, t.2.2.2.1,
      t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2)) hbrest)

end NearQuarticWires.StageLift
