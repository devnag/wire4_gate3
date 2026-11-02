import Proof.Quartic.StageGamma.CoefficientPair

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: positive
and negative coefficient components occupy separate binary variables. -/
def coefficientPositive : Fin VV := ⟨88, by decide⟩
def coefficientNegative : Fin VV := ⟨89, by decide⟩
def coefficientTempPositive : Fin VV := ⟨90, by decide⟩
def coefficientTempNegative : Fin VV := ⟨91, by decide⟩

/-- `cor:conditional`, paper/paper.tex: exactly
these four binary variables are changed by signed coefficient scaling. -/
def coefficientScratch : List (Fin VV) :=
  [coefficientPositive, coefficientNegative, coefficientTempPositive, coefficientTempNegative]

/-- `cor:conditional`, paper/paper.tex: one positive
factor physically scales each sign component without numerical cancellation. -/
def multiplyPairPositive (factor : Fin VV) : St VV MM :=
  .seq (.op (.mul coefficientPositive factor coefficientTempPositive))
    (.seq (.op (.mul coefficientNegative factor coefficientTempNegative))
      (.seq (.op (.copy coefficientPositive coefficientTempPositive))
        (.op (.copy coefficientNegative coefficientTempNegative))))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: four actual binary operations multiply the signed natural
pair by a positive factor, preserving every ORIGINAL source variable. -/
theorem multiplyPairPositive_run (C : Ctx) (factor : Fin VV)
    (hfactor : factor ∉ coefficientScratch) (a : DS VV MM) (hc : Cst a)
    (p : CoefficientPair) (f : ℕ)
    (hp : a.env coefficientPositive = p.positive)
    (hn : a.env coefficientNegative = p.negative) (hf : a.env factor = f)
    (hpf : p.positive * f < 2 ^ C.Wd) (hnf : p.negative * f < 2 ^ C.Wd) :
    Hs C (multiplyPairPositive factor) a 7 (fun b =>
      b.env coefficientPositive = p.positive * f ∧
      b.env coefficientNegative = p.negative * f ∧ Same a b ∧ Cst b ∧
      Fr a b coefficientScratch) := by
  have hfp : coefficientPositive ≠ factor := by intro h; exact hfactor (by simp [coefficientScratch, ← h])
  have hfn : coefficientNegative ≠ factor := by intro h; exact hfactor (by simp [coefficientScratch, ← h])
  have hftp : factor ≠ coefficientTempPositive := by intro h; exact hfactor (by simp [coefficientScratch, h])
  have hftn : factor ≠ coefficientTempNegative := by intro h; exact hfactor (by simp [coefficientScratch, h])
  unfold multiplyPairPositive
  refine Hs.seq (t1 := 1) (t2 := 5)
    (hs_mul C coefficientPositive factor coefficientTempPositive a hfp (by decide) hftp
      (by rw [hp, hf]; exact hpf)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_mul C coefficientNegative factor coefficientTempNegative _ hfn (by decide) hftn
      (by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ hftp, hn, hf]; exact hnf)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_copy C coefficientPositive coefficientTempPositive _ (by decide)) ?_
  intro b hb
  subst hb
  refine Hs.mono (hs_copy C coefficientNegative coefficientTempNegative _ (by decide)) le_rfl ?_
  rintro b rfl
  have hh : Fr a
      ((((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).set
        coefficientTempNegative
        ((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env coefficientNegative *
          (a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env factor)).set
        coefficientPositive
        (((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).set
          coefficientTempNegative
          ((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env coefficientNegative *
            (a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env factor)).env
              coefficientTempPositive)).set coefficientNegative
        ((((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).set
          coefficientTempNegative
          ((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env coefficientNegative *
            (a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env factor)).set
          coefficientPositive
          (((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).set
            coefficientTempNegative
            ((a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env coefficientNegative *
              (a.set coefficientTempPositive (a.env coefficientPositive * a.env factor)).env factor)).env
                coefficientTempPositive)).env coefficientTempNegative)) coefficientScratch :=
    (Fr.set _ _ (by simp [coefficientScratch])).trans
      ((Fr.set _ _ (by simp [coefficientScratch])).trans
        ((Fr.set _ _ (by simp [coefficientScratch])).trans
          (Fr.set _ _ (by simp [coefficientScratch]))))
  refine ⟨?_, ?_, (Same.set _ _ _).trans ((Same.set _ _ _).trans
    ((Same.set _ _ _).trans (Same.set _ _ _))), Cst.of_fr hc hh (by decide), hh⟩
  · vsimp [hp, hf, hftp]
  · vsimp [hn, hf, hftp]

end NearQuarticWires.StageGamma
