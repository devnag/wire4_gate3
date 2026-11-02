import Proof.Quartic.StageLift.Token
import Proof.Quartic.StageRecovery.ModNegate
import Proof.Quartic.StageRecovery.ModReduce

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery

/-- `lem:print` and `lem:residue`, paper/paper.tex: normalize a computed signed coefficient before any
postfix coefficient token is emitted. -/
def reduceSignedCoefficient : St VV MM :=
  .seq reduceLeftProgram (.ite (.eq signVar v1) (negateModProgram leftVar) skipS)

/-- `lem:print` and `lem:residue`, paper/paper.tex: binary coefficient normalization preserves the source
and produces the exact bounded residue, including negative zero. -/
theorem reduceSignedCoefficient_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q magnitude : ℕ) (negative : Bool) (hq : 0 < q)
    (haq : a.env modulusVar = q) (ham : a.env leftVar = magnitude)
    (has : a.env signVar = negative.toNat) (hfit : 2 * q ≤ 2 ^ C.Wd) :
    Hs C reduceSignedCoefficient a 12 (fun b =>
      b.env leftVar = signedNaturalResidue q magnitude negative ∧ b.sh = a.sh ∧
      Cst b ∧ Fr a b [leftVar, productVar, quotientVar, remainderVar, vJ]) := by
  unfold reduceSignedCoefficient
  refine Hs.seq (t2 := 8) (reduceLeftProgram_spec C a (by rw [haq]; exact hq)
    (by rw [haq]; exact hfit)) fun b ⟨hbl, hbsh, hbf⟩ => ?_
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
  have hbs : b.env signVar = negative.toNat := by rw [hbf _ (by decide), has]
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hbl' : b.env leftVar = magnitude % q := by simpa only [ham, haq] using hbl
  cases negative with
  | false =>
      have ht : (Cnd.eq signVar v1).eval b = false := by simp [Cnd.eval, hbs, hbc.one]
      refine (Hs.iteF (c := .eq signVar v1) (show signVar ≠ v1 by decide) ht
        (skip_spec b)).mono (by omega) ?_
      rintro d rfl
      exact ⟨by simpa (config := {decide := true}) [DS.set, signedNaturalResidue] using hbl',
        hbsh, Cst.of_fr (T := [vJ]) hbc (Fr.set b 0 (by simp)) (by decide),
        Fr.trans (Fr.weaken hbf (by simp)) (Fr.set b 0 (by simp))⟩
  | true =>
      have ht : (Cnd.eq signVar v1).eval b = true := by simp [Cnd.eval, hbs, hbc.one]
      refine (Hs.iteT (c := .eq signVar v1) (show signVar ≠ v1 by decide) ht
        (negateModProgram_spec C b leftVar (by decide) (by rw [hbq]; exact hq)
          (by rw [hbq]; exact hfit)
          (by rw [hbl', hbq]; exact (Nat.mod_lt _ hq).le))).mono le_rfl ?_
      rintro d ⟨hdl, hdsh, hdf⟩
      exact ⟨by simpa only [signedNaturalResidue, if_true, hbl', hbq] using hdl,
        hdsh.trans hbsh, Cst.of_fr hbc hdf (by decide),
        Fr.trans (Fr.weaken hbf (by simp)) (Fr.weaken hdf (by simp))⟩

/-- `lem:print`, paper/paper.tex: every generated
coefficient is reduced before its canonical constant token is written. -/
def emitReducedCoefficient : St VV MM :=
  .seq reduceSignedCoefficient (emitNaturalConstant leftVar)

/-- `lem:print`, paper/paper.tex: the physical
coefficient token depends on the requested modulus rather than an
unbounded intermediate polynomial value. -/
theorem emitReducedCoefficient_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q magnitude : ℕ) (negative : Bool) (hq : 0 < q)
    (haq : a.env modulusVar = q) (ham : a.env leftVar = magnitude)
    (has : a.env signVar = negative.toNat) (hfit : 2 * q ≤ 2 ^ C.Wd)
    (hW : 2 ≤ C.Wd)
    (hbits : NearCubicWires.natBitLength (signedNaturalResidue q magnitude negative) + 2 < 2 ^ C.Wd) :
    Hs C emitReducedCoefficient a
      (40 * NearCubicWires.natBitLength (signedNaturalResidue q magnitude negative) + 69) (fun b =>
      b.out = a.out ++ NearCubicGates.Close.Interfaces.Formats.tokWord
        (.const (signedNaturalResidue q magnitude negative : ℤ)) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (leftVar :: productVar :: quotientVar :: remainderVar :: tokenScratch)) := by
  unfold emitReducedCoefficient
  refine (Hs.seq (t2 := 40 * NearCubicWires.natBitLength
      (signedNaturalResidue q magnitude negative) + 56)
    (reduceSignedCoefficient_spec C a hc q magnitude negative hq haq ham has hfit)
    fun b ⟨hbl, hbsh, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have he := emitNaturalConstant_spec C leftVar (by decide) (by decide) b hbc hW
    (by rw [hbl]; exact hbits)
  rw [hbl] at he
  refine he.mono le_rfl ?_
  rintro d ⟨hdo, hdr, hdc, hdf⟩
  have hs := Same.of_sh hbsh
  exact ⟨by rw [hdo, hs.out], hdr.trans (by rw [hs.ip, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc]),
    hdc, Fr.trans (Fr.weaken hbf (by simp [tokenScratch]))
      (Fr.weaken hdf (by intro y hy; simp only [List.mem_cons]; tauto))⟩

end NearQuarticWires.StageLift
