import Proof.Quartic.StageRecovery.ModArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery

/-- `lem:print` and `lem:residue`, paper/paper.tex: the current binary place value is reduced after every
payload bit, independently of the original integer's bit length. -/
def streamPowerVar : Fin VV := 124

/-- `lem:print`, paper/paper.tex: one actual
binary doubling is immediately reduced by the requested modulus. -/
def doubleStreamPower : St VV MM :=
  .seq (.op (.shl streamPowerVar))
    (.seq (.op (.dm streamPowerVar modulusVar quotientVar remainderVar))
      (.op (.copy streamPowerVar remainderVar)))

/-- `lem:print`, paper/paper.tex: doubling never
constructs an unbounded power of two in an arithmetic register. -/
theorem doubleStreamPower_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q power : ℕ) (hq : 0 < q) (haq : a.env modulusVar = q)
    (hap : a.env streamPowerVar = power) (hp : power < q)
    (hfit : 2 * q ≤ 2 ^ C.Wd) :
    Hs C doubleStreamPower a 5 (fun b =>
      b.env streamPowerVar = (2 * power) % q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [streamPowerVar, quotientVar, remainderVar]) := by
  unfold doubleStreamPower
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_shl C streamPowerVar a (by rw [hap]; omega)) fun b hb => ?_
  subst b
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_dm C streamPowerVar modulusVar quotientVar remainderVar _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simpa (config := {decide := true}) [DS.set, haq] using hq)
      (by simpa (config := {decide := true}) [DS.set, haq] using hfit)) fun b hb => ?_
  subst b
  refine (hs_copy C streamPowerVar remainderVar _ (by decide)).mono le_rfl ?_
  rintro b rfl
  have hf : Fr a
      ((((a.set streamPowerVar (2 * a.env streamPowerVar)).set quotientVar
        ((2 * a.env streamPowerVar) / q)).set remainderVar
        ((2 * a.env streamPowerVar) % q)).set streamPowerVar ((2 * a.env streamPowerVar) % q))
      [streamPowerVar, quotientVar, remainderVar] :=
    (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp (config := {decide := true}) [DS.set, hap, haq]
  · exact ⟨by simpa (config := {decide := true}) [DS.set] using hc.z,
      by simpa (config := {decide := true}) [DS.set] using hc.one,
      by simpa (config := {decide := true}) [DS.set] using hc.two⟩
  · simpa (config := {decide := true}) [DS.set, haq] using hf

/-- `lem:print`, paper/paper.tex: a payload one
adds the current reduced place value; a payload zero adds nothing. -/
def addStreamBit : St VV MM :=
  .ite (.eq t1 v1) (.seq (.op (.copy rightVar streamPowerVar)) addModProgram) skipS

/-- `lem:print`, paper/paper.tex: each actual
payload bit updates only the reduced accumulator, with every addition
and division bounded by the actual modulus rather than the raw index. -/
theorem addStreamBit_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q value power : ℕ) (bit : Bool) (hq : 0 < q)
    (haq : a.env modulusVar = q) (hav : a.env leftVar = value)
    (hap : a.env streamPowerVar = power) (hab : a.env t1 = bit.toNat)
    (hv : value < q) (hp : power < q) (hfit : 2 * q ≤ 2 ^ C.Wd) :
    Hs C addStreamBit a 8 (fun b =>
      b.env leftVar = (value + if bit then power else 0) % q ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [leftVar, rightVar, quotientVar, remainderVar, vJ]) := by
  unfold addStreamBit
  cases bit with
  | false =>
      have ht : (Cnd.eq t1 v1).eval a = false := by simp [Cnd.eval, hab, hc.one]
      refine (Hs.iteF (c := .eq t1 v1) (show t1 ≠ v1 by decide) ht (skip_spec a)).mono
        (by omega) ?_
      rintro b rfl
      have hf : Fr a (a.set vJ 0) [leftVar, rightVar, quotientVar, remainderVar, vJ] :=
        Fr.set a _ (by simp)
      exact ⟨by simp (config := {decide := true}) [DS.set, hav, Nat.mod_eq_of_lt hv],
        rfl, Cst.of_fr hc hf (by decide), hf⟩
  | true =>
      have ht : (Cnd.eq t1 v1).eval a = true := by simp [Cnd.eval, hab, hc.one]
      refine Hs.iteT (c := .eq t1 v1) (show t1 ≠ v1 by decide) ht ?_
      refine Hs.seq (t1 := 1) (t2 := 5) (hs_copy C rightVar streamPowerVar a (by decide))
        fun b hb => ?_
      subst b
      let b := a.set rightVar (a.env streamPowerVar)
      have hbc : Cst b := Cst.of_fr hc (Fr.set (T := [rightVar]) a _ (by simp)) (by decide)
      have hbq : b.env modulusVar = q := by simpa (config := {decide := true}) [b, DS.set] using haq
      have hbl : b.env leftVar = value := by simpa (config := {decide := true}) [b, DS.set] using hav
      have hbr : b.env rightVar = power := by simp [b, hap]
      refine (addModProgram_spec C b (by rw [hbq]; exact hq) (by rw [hbq]; exact hfit)
        (by rw [hbl, hbr]; omega)).mono le_rfl ?_
      rintro d ⟨hdl, hdsh, hdf⟩
      have hf : Fr a d [leftVar, rightVar, quotientVar, remainderVar, vJ] :=
        (Fr.set (T := [leftVar, rightVar, quotientVar, remainderVar, vJ]) a _ (by simp)).trans
          (hdf.weaken (by simp))
      exact ⟨by simpa only [hbl, hbr, hbq, Bool.true_eq, if_true] using hdl,
        hdsh, Cst.of_fr hbc hdf (by decide), hf⟩

end NearQuarticWires.StageLift
