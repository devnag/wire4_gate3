import Proof.Quartic.StageRecovery.ModReduce

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the literal Boolean
coordinate of a characteristic assignment, represented as zero or one. -/
def pointBit (point atom : ℕ) : ℕ := if point.testBit atom then 1 else 0

/-- `lem:print`, paper/paper.tex: halving the assignment
and reducing modulo two recovers the actual original atom coordinate. -/
theorem pointBit_eq (point atom : ℕ) : pointBit point atom = point / 2 ^ atom % 2 := by
  unfold pointBit
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (point / 2 ^ atom) with h | h <;> simp [h]

/-- `lem:print`, paper/paper.tex: a variable token reads
its characteristic coordinate by binary halving, then normalizes to a bit. -/
def variableBitProgram : St VV MM :=
  .seq (.op (.copy leftVar pointVar))
    (.seq (forS c0 atomVar (.op (.half leftVar)))
      (.seq (.op (.dm leftVar v2 quotientVar remainderVar))
        (.op (.copy leftVar remainderVar))))

/-- `lem:print`, paper/paper.tex: the actual variable
coordinate extraction has a number of arithmetic operations linear in
the original atom index and retains the rest of the formula state. -/
theorem variableBitProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (point atom : ℕ) (hap : a.env pointVar = point) (haa : a.env atomVar = atom)
    (hafit : atom < 2 ^ C.Wd) (hW : 4 ≤ 2 ^ C.Wd) :
    Hs C variableBitProgram a (atom * 5 + 10) (fun b =>
      b.env leftVar = pointBit point atom ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [leftVar, c0, quotientVar, remainderVar]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env leftVar = point / 2 ^ k ∧ b.sh = a.sh ∧ Cst b ∧ Fr a b [leftVar, c0]
  unfold variableBitProgram
  refine (Hs.seq (t2 := atom * 5 + 8) (hs_copy C leftVar pointVar a (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  have ef := forS_spec' (C := C) c0 atomVar (by decide) (.op (.half leftVar))
    (a.set leftVar (a.env pointVar)) atom hafit I 1
    (fun k b value ⟨hl, hs, hbc, hbf⟩ =>
      ⟨by simpa (config := {decide := true}) [DS.set] using hl, hs,
        Cst.of_fr (T := [c0]) hbc (Fr.set _ _ (by decide)) (by decide),
        Fr.trans hbf (Fr.set _ _ (by decide))⟩)
    ⟨by simp [hap], rfl, Cst.of_fr (T := [leftVar]) hc (Fr.set _ _ (by decide)) (by decide),
      Fr.set _ _ (by decide)⟩
    (by simpa (config := {decide := true}) [DS.set] using haa) ?_
  · refine (Hs.seq (t2 := 3) ef fun b ⟨⟨hl, hs, hbc, hbf⟩, _, _⟩ => ?_).mono
      (by omega) (fun _ h => h)
    refine Hs.seq (t2 := 1) (hs_dm C leftVar v2 quotientVar remainderVar b
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hbc.two]; omega) (by rw [hbc.two]; omega)) fun d hd => ?_
    subst d
    refine (hs_copy C leftVar remainderVar _ (by decide)).mono le_rfl ?_
    rintro d rfl
    refine ⟨?_, hs, ?_, ?_⟩
    · simp only [DS.set_env_self, hl, hbc.two, pointBit_eq]
    · exact Cst.of_fr (T := [quotientVar, remainderVar, leftVar]) hbc
        (Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))) (by decide)
    · exact Fr.trans (Fr.weaken hbf (by decide))
        (Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  · intro k hk b ⟨hl, hs, hbc, hbf⟩ hctr he
    refine (hs_half C leftVar b).mono le_rfl ?_
    rintro d rfl
    refine ⟨⟨?_, hs, Cst.of_fr (T := [leftVar]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by decide))⟩,
      by simpa (config := {decide := true}) [DS.set] using hctr,
      by simpa (config := {decide := true}) [DS.set] using he⟩
    rw [DS.set_env_self, hl, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

end NearQuarticWires.StageRecovery
