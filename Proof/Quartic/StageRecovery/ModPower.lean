import Proof.Quartic.StageRecovery.ModArithmetic
import Proof.Gates.Cells.Loop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the literal unary
formula exponent retained by the modular postfix evaluator. -/
def exponentVar : Fin VV := ⟨77, by decide⟩

/-- `lem:print`, paper/paper.tex: repeated binary
multiplication reduces every intermediate power before the next step. -/
def powerModProgram : St VV MM :=
  .seq (.op (.copy leftVar v1)) (forS c0 exponentVar multiplyModProgram)

/-- `lem:print`, paper/paper.tex: the actual modular
power loop has a charged number of arithmetic operations linear in
the formula exponent, never in the modulus's numeric value. -/
theorem powerModProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q base exponent : ℕ) (hq : 2 ≤ q) (hbase : base < q)
    (haq : a.env modulusVar = q) (hab : a.env rightVar = base)
    (hae : a.env exponentVar = exponent) (hexp : exponent < 2 ^ C.Wd)
    (hqfit : 2 * q ≤ 2 ^ C.Wd) (hproduct : q * q < 2 ^ C.Wd) :
    Hs C powerModProgram a (exponent * 9 + 6) (fun b =>
      b.env leftVar = base ^ exponent % q ∧ b.env rightVar = base ∧
      b.env modulusVar = q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [leftVar, productVar, quotientVar, remainderVar, c0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env leftVar = base ^ k % q ∧ b.env rightVar = base ∧
      b.env modulusVar = q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [leftVar, productVar, quotientVar, remainderVar, c0]
  unfold powerModProgram
  refine (Hs.seq (t2 := exponent * 9 + 4) (hs_copy C leftVar v1 a (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine (forS_spec' c0 exponentVar (by decide) multiplyModProgram _ exponent hexp I 5
    (fun k b v ⟨hl, hr, hm, hs, hbc, hbf⟩ => ?_) ?_
    (by simpa (config := {decide := true}) [DS.set] using hae) ?_).mono (by omega) ?_
  · exact ⟨by simpa (config := {decide := true}) [DS.set] using hl,
      by simpa (config := {decide := true}) [DS.set] using hr,
      by simpa (config := {decide := true}) [DS.set] using hm, hs,
      Cst.of_fr (T := [c0]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by decide))⟩
  · refine ⟨?_, ?_, ?_, rfl, ?_, Fr.set _ _ (by decide)⟩
    · simp (config := {decide := true}) [DS.set, hc.one, Nat.mod_eq_of_lt (show 1 < q by omega)]
    · simpa (config := {decide := true}) [DS.set] using hab
    · simpa (config := {decide := true}) [DS.set] using haq
    · exact Cst.of_fr (T := [leftVar]) hc (Fr.set _ _ (by decide)) (by decide)
  · intro k hk b ⟨hl, hr, hm, hs, hbc, hbf⟩ hctr he
    have hrem : base ^ k % q < q := Nat.mod_lt _ (by omega)
    have hmul : b.env leftVar * b.env rightVar < 2 ^ C.Wd := by
      rw [hl, hr]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right base hrem.le)
        ((Nat.mul_lt_mul_of_pos_left hbase (by omega)).trans hproduct)
    refine (multiplyModProgram_spec C b (by rw [hm]; omega)
      (by rw [hm]; exact hqfit) hmul).mono le_rfl ?_
    rintro d ⟨hdl, hdsh, hdf⟩
    refine ⟨⟨?_, by rw [hdf _ (by decide), hr], by rw [hdf _ (by decide), hm],
      hdsh.trans hs, Cst.of_fr hbc hdf (by decide),
      Fr.trans hbf (Fr.weaken hdf (by decide))⟩,
      by rw [hdf _ (by decide), hctr], by rw [hdf _ (by decide), he]⟩
    rw [hdl, hl, hr, hm, pow_succ, Nat.mod_mul_mod]
  · rintro b ⟨hb, _, _⟩
    exact hb

end NearQuarticWires.StageRecovery
