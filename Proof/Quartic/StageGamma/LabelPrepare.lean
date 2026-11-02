import Proof.Quartic.StageGamma.BinaryPower

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: digit zero
contributes no equation; a positive digit physically computes label digit−1. -/
def prepareLabel (slot : Fin 8) : St VV MM :=
  .seq (.op (.copy (gammaLabel slot) (gammaDigit slot)))
    (.ite (.eq (gammaDigit slot) vZ) skipS (.op (.sub (gammaLabel slot) v1)))

/-- `cor:conditional`, paper/paper.tex: true selected
sample indices are obtained by paid binary operations with no field padding. -/
theorem prepareLabel_run (C : Ctx) (slot : Fin 8) (a : DS VV MM) (hc : Cst a) :
    Hs C (prepareLabel slot) a 4 (fun b =>
      b.env (gammaLabel slot) = a.env (gammaDigit slot) - 1 ∧ Same a b ∧ Cst b ∧
      Fr a b [gammaLabel slot, vJ]) := by
  have hd : gammaLabel slot ≠ gammaDigit slot := by
    fin_cases slot <;> decide
  have hdz : gammaDigit slot ≠ vZ := by
    fin_cases slot <;> decide
  have hl1 : gammaLabel slot ≠ v1 := by
    fin_cases slot <;> decide
  have hlj : gammaLabel slot ≠ vJ := by
    fin_cases slot <;> decide
  have hconst : vZ ∉ [gammaLabel slot, vJ] ∧ v1 ∉ [gammaLabel slot, vJ] ∧
      v2 ∉ [gammaLabel slot, vJ] := by
    fin_cases slot <;> decide
  unfold prepareLabel
  refine Hs.seq (t1 := 1) (t2 := 2)
    (hs_copy C (gammaLabel slot) (gammaDigit slot) a hd) ?_
  intro b hb
  subst hb
  let b := a.set (gammaLabel slot) (a.env (gammaDigit slot))
  have hbc : Cst b := Cst.of_fr hc (Fr.set a _ (by simp)) hconst
  have hbf : Fr a b [gammaLabel slot, vJ] := Fr.set a _ (by simp)
  have hbd : b.env (gammaDigit slot) = a.env (gammaDigit slot) := by
    exact DS.set_env_ne _ _ hd.symm
  have hbl : b.env (gammaLabel slot) = a.env (gammaDigit slot) := by simp [b]
  refine Hs.ite (c := .eq (gammaDigit slot) vZ) (t := 1) hdz ?_ ?_
  · intro hz
    have hv : a.env (gammaDigit slot) = 0 := by
      have hh : b.env (gammaDigit slot) = b.env vZ := of_decide_eq_true hz
      rwa [hbd, hbc.z] at hh
    refine Hs.mono (skip_spec b) le_rfl ?_
    rintro d rfl
    exact ⟨by rw [DS.set_env_ne _ _ hlj, hbl, hv],
      (Same.set a _ _).trans (Same.set b _ _),
      Cst.of_fr hbc (Fr.set b 0 (by simp : vJ ∈ [gammaLabel slot, vJ])) hconst,
      hbf.trans (Fr.set b 0 (by simp))⟩
  · intro hn
    have hv : 1 ≤ a.env (gammaDigit slot) := by
      have hh : a.env (gammaDigit slot) ≠ 0 := by
        have hne : b.env (gammaDigit slot) ≠ b.env vZ := of_decide_eq_false hn
        rwa [hbd, hbc.z] at hne
      omega
    refine Hs.mono (hs_sub C (gammaLabel slot) v1 b hl1 (by rw [hbl, hbc.one]; exact hv)) le_rfl ?_
    rintro d rfl
    exact ⟨by simp [hbl, hbc.one],
      (Same.set a _ _).trans (Same.set b _ _),
      Cst.of_fr hbc (Fr.set b _ (by simp : gammaLabel slot ∈ [gammaLabel slot, vJ])) hconst,
      hbf.trans (Fr.set b _ (by simp))⟩

end NearQuarticWires.StageGamma
