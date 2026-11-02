import Proof.Quartic.StageLift.TargetAddress
import Proof.Quartic.StageLift.Token
import Proof.Quartic.StageLift.FormulaBytes

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:residue`, paper/paper.tex: actual
normalized index records and the digit-prime reduction workspace. -/
def targetRaw : Fin VV := 64
def targetQuotient : Fin VV := 65
def targetValue : Fin VV := 68

/-- `lem:residue` and Step 3, paper/paper.tex: score targets are read from the real normalized bank
and immediately serialized, without a supplied target value. -/
def emitScoreTarget : St VV MM :=
  .seq (fetch indexStore targetAddress targetRaw) (emitNaturalConstant targetRaw)

/-- `lem:residue` and Step 3, paper/paper.tex: digit targets are read modulo q, then physically
reduced modulo the actual selected prime before being serialized. -/
def emitDigitTarget : St VV MM :=
  .seq (fetch indexStore targetAddress targetRaw)
    (.seq (.op (.dm targetRaw degreePrime targetQuotient targetValue))
      (emitNaturalConstant targetValue))

/-- `lem:residue` and `lem:print`, paper/paper.tex: a score-target token is supplied by an actual paid
record-store fetch and canonical integer output, not an external rho. -/
theorem emitScoreTarget_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (B : ℕ)
    (haddress : a.env targetAddress < (a.ram indexStore).length)
    (hfit : a.env targetAddress < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hbits : natBitLength ((a.ram indexStore).getD (a.env targetAddress) 0) ≤ B)
    (hBit : B + 2 < 2 ^ C.Wd) :
    Hs C emitScoreTarget a (a.rc indexStore + 5 * a.env targetAddress + 40 * B + 66)
      (fun b => b.out = a.out ++ tokWord (.const
        (((a.ram indexStore).getD (a.env targetAddress) 0 : ℕ) : ℤ)) ∧
        b.rc = Function.update a.rc indexStore (a.env targetAddress + 1) ∧
        (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
        Cst b ∧ Fr a b ([c0, vJ, targetRaw] ++ tokenScratch)) := by
  unfold emitScoreTarget
  refine (Hs.seq (t2 := 40 * B + 56)
    (fetch_spec (C := C) indexStore targetAddress targetRaw (by decide) (by decide) a haddress hfit)
    fun b ⟨hbv, hbi, hbo, hbram, hbrc, hbkin, hbkout, hbkc, hbf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hbfit : natBitLength (b.env targetRaw) + 2 < 2 ^ C.Wd := by rw [hbv]; omega
  refine (emitNaturalConstant_spec C targetRaw (by decide) (by decide) b hbc hW hbfit).mono
    (by rw [hbv]; omega) ?_
  rintro d ⟨hdo, hdrest, hdc, hdf⟩
  refine ⟨by rw [hdo, hbo, hbv], ?_, ?_, hdc,
    (hbf.weaken (by simp)).trans (hdf.weaken (by intro x hx; simp only [List.mem_append]; tauto))⟩
  · rw [show d.rc = b.rc from congrArg (fun t => t.2.2.1) hdrest, hbrc]
  · exact (congrArg (fun t => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdrest).trans
      (by rw [hbi, hbram, hbkin, hbkout, hbkc])

/-- `lem:residue` and `lem:print`, paper/paper.tex: a digit token is computed from the real stored q-residue
by actual division with the selected prime. Its binary charge depends
on the prime, independently of the original raw digit magnitude. -/
theorem emitDigitTarget_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (prime : ℕ) (hp : 0 < prime) (hprime : a.env degreePrime = prime)
    (haddress : a.env targetAddress < (a.ram indexStore).length)
    (hfit : a.env targetAddress < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hcap : 2 * prime ≤ 2 ^ C.Wd) (hBit : natBitLength prime + 2 < 2 ^ C.Wd) :
    Hs C emitDigitTarget a
      (a.rc indexStore + 5 * a.env targetAddress + 40 * natBitLength prime + 68)
      (fun b => b.out = a.out ++ tokWord (.const
        ((((a.ram indexStore).getD (a.env targetAddress) 0) % prime : ℕ) : ℤ)) ∧
        b.rc = Function.update a.rc indexStore (a.env targetAddress + 1) ∧
        (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
        Cst b ∧ Fr a b ([c0, vJ, targetRaw, targetQuotient, targetValue] ++ tokenScratch)) := by
  unfold emitDigitTarget
  refine (Hs.seq (t2 := 40 * natBitLength prime + 58)
    (fetch_spec (C := C) indexStore targetAddress targetRaw (by decide) (by decide) a haddress hfit)
    fun b ⟨hbv, hbi, hbo, hbram, hbrc, hbkin, hbkout, hbkc, hbf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hbp : b.env degreePrime = prime := (hbf _ (by decide)).trans hprime
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  refine (Hs.seq (t2 := 40 * natBitLength prime + 56)
    (hs_dm C targetRaw degreePrime targetQuotient targetValue b
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hbp]; exact hp) (by rw [hbp]; exact hcap)) fun d hd => ?_).mono
        (by omega) (fun _ h => h)
  subst d
  let d := (b.set targetQuotient (b.env targetRaw / b.env degreePrime)).set
    targetValue (b.env targetRaw % b.env degreePrime)
  have hdv : d.env targetValue = (a.ram indexStore).getD (a.env targetAddress) 0 % prime := by
    simp only [d, DS.set_env_self, hbv, hbp]
  have hdf : Fr b d [targetQuotient, targetValue] :=
    (Fr.set b _ (by simp)).trans (Fr.set _ _ (by simp))
  have hdc : Cst d := Cst.of_fr hbc hdf (by decide)
  have hbits := codec_nbl_mono (Nat.mod_lt ((a.ram indexStore).getD (a.env targetAddress) 0) hp).le
  refine (emitNaturalConstant_spec C targetValue (by decide) (by decide) d hdc hW
    (by rw [hdv]; omega)).mono (by rw [hdv]; omega) ?_
  rintro z ⟨hzo, hzrest, hzc, hzf⟩
  have hf : Fr a z ([c0, vJ, targetRaw, targetQuotient, targetValue] ++ tokenScratch) :=
    (hbf.weaken (by simp)).trans ((hdf.weaken (by simp)).trans
      (hzf.weaken (by intro x hx; simp only [List.mem_append]; tauto)))
  refine ⟨by rw [hzo, show d.out = b.out from rfl, hbo, hdv], ?_, ?_, hzc, hf⟩
  · rw [show z.rc = d.rc from congrArg (fun t => t.2.2.1) hzrest]
    exact hbrc
  · exact (congrArg (fun t => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hzrest).trans
      (by change (b.ip, b.ram, b.kin, b.kout, b.kc) = _
          rw [hbi, hbram, hbkin, hbkout, hbkc])

end NearQuarticWires.StageLift
