import Proof.Quartic.StageRecovery.ModMetadata

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: an input integer's
magnitude is reduced before its first arithmetic formula operation. -/
def reduceLeftProgram : St VV MM :=
  .seq (.op (.dm leftVar modulusVar quotientVar remainderVar))
    (.op (.copy leftVar remainderVar))

/-- `lem:print`, paper/paper.tex: the literal binary
division reduces the decoded magnitude without altering input or
output cursors or any retained formula metadata. -/
theorem reduceLeftProgram_spec (C : Ctx) (a : DS VV MM)
    (hq : 0 < a.env modulusVar) (hfit : 2 * a.env modulusVar ≤ 2 ^ C.Wd) :
    Hs C reduceLeftProgram a 3 (fun b =>
      b.env leftVar = a.env leftVar % a.env modulusVar ∧ b.sh = a.sh ∧
      Fr a b [leftVar, quotientVar, remainderVar]) := by
  unfold reduceLeftProgram
  refine Hs.seq (t2 := 1) (hs_dm C leftVar modulusVar quotientVar remainderVar a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq hfit) fun b hb => ?_
  subst b
  refine (hs_copy C leftVar remainderVar _ (by decide)).mono le_rfl ?_
  rintro b rfl
  exact ⟨rfl, rfl, Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩

/-- `lem:residue`, paper/paper.tex: the magnitude/sign
representation of an integer constant gives its exact nonnegative
residue under the actual recovery modulus. -/
def signedNaturalResidue (q magnitude : ℕ) (negative : Bool) : ℕ :=
  if negative then (q - magnitude % q) % q else magnitude % q

/-- `lem:residue`, paper/paper.tex: binary magnitude
reduction and modular sign normalization recover the literal integer
constant modulo the requested modulus. -/
theorem signedNaturalResidue_eq (q : ℕ) (hq : 0 < q) (value : ℤ) :
    (signedNaturalResidue q value.natAbs (decide (value < 0)) : ℤ) = value % (q : ℤ) := by
  have hr := Nat.mod_lt value.natAbs hq
  have hm : ((value.natAbs % q : ℕ) : ℤ) ≡ (value.natAbs : ℤ) [ZMOD (q : ℤ)] := by
    rw [Int.natCast_mod]
    exact Int.mod_modEq _ _
  by_cases hv : value < 0
  · simp only [signedNaturalResidue, hv, decide_true, if_true, Int.natCast_mod]
    rw [Nat.cast_sub hr.le]
    have hz : (q : ℤ) ≡ 0 [ZMOD (q : ℤ)] := by simp [Int.ModEq]
    have h := hz.sub hm
    have he : -(value.natAbs : ℤ) = value := by
      rw [Int.natCast_natAbs, abs_of_neg hv, neg_neg]
    simpa only [Int.ModEq, zero_sub, he] using h
  · simp only [signedNaturalResidue, hv, decide_false, Bool.false_eq_true, if_false]
    rw [Int.natCast_mod, Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ value)]

end NearQuarticWires.StageRecovery
