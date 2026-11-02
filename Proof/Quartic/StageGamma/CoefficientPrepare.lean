import Proof.Quartic.StageGamma.CoefficientLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open scoped BigOperators
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the exact
signed natural pair for the ORIGINAL eight-slot choice product. -/
def originalCoefficientPair (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : CoefficientPair :=
  coefficientPairFold request.parameters.N request.parameters.Q choice
    (List.finRange 8) ⟨1, 0⟩

/-- `cor:conditional`, paper/paper.tex: the actual
two-register coefficient has exactly the ORIGINAL signed product value. -/
theorem originalCoefficientPair_value (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (originalCoefficientPair request choice).value =
      Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice := by
  rw [originalCoefficientPair, coefficientPairFold_value]
  simp only [CoefficientPair.value, Nat.cast_one, Nat.cast_zero, sub_zero, one_mul]
  simpa only [Cycle.gammaChoiceWeight] using
    (Fin.prod_univ_def (fun slot : Fin 8 =>
      Cycle.choiceCoefficient request.parameters.N request.parameters.Q (choice slot))).symm

/-- `prop:time`, paper/paper.tex: no signed
cancellation is needed to bound the two actual coefficient registers. -/
theorem originalCoefficientPair_mass_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (originalCoefficientPair request choice).positive +
      (originalCoefficientPair request choice).negative ≤ 2 ^ Cycle.seedLength request.parameters := by
  have hh := coefficientPairFold_mass_le request choice (List.finRange 8)
  simpa only [originalCoefficientPair, List.length_finRange, Cycle.seedLength, Nat.mul_comm] using hh

/-- `cor:conditional`, paper/paper.tex: N² is
formed by physical binary multiplication from the actual prepared side. -/
def prepareSideSquare : St VV MM :=
  .seq (.op (.copy coefficientTempPositive gammaSide))
    (.op (.mul gammaSide coefficientTempPositive gammaSideSquare))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the square factor used by every actual negative sample
coefficient is physically computed, with overflow derived from ORIGINAL kh. -/
theorem prepareSideSquare_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (hc : Cst a) (hside : a.env gammaSide = request.parameters.N)
    (hwidth : Cycle.seedLength request.parameters + 1 ≤ C.Wd) :
    Hs C prepareSideSquare a 3 (fun b =>
      b.env gammaSideSquare = request.parameters.N ^ 2 ∧ Same a b ∧ Cst b ∧
      Fr a b [gammaSideSquare, coefficientTempPositive]) := by
  have hfit : request.parameters.N ^ 2 < 2 ^ C.Wd := by
    change (2 ^ request.parameters.kh) ^ 2 < _
    rw [← pow_mul]
    apply Nat.pow_lt_pow_right (by decide)
    have hh := request.parameters.k_le
    dsimp [Cycle.seedLength] at hwidth
    omega
  unfold prepareSideSquare
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_copy C coefficientTempPositive gammaSide a (by decide)) ?_
  intro b hb
  subst hb
  refine Hs.mono (hs_mul C gammaSide coefficientTempPositive gammaSideSquare _
    (by decide) (by decide) (by decide) (by vsimp [hside]; simpa [pow_two] using hfit)) le_rfl ?_
  rintro b rfl
  exact ⟨by vsimp [hside, pow_two], (Same.set _ _ _).trans (Same.set _ _ _),
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩,
    (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))⟩

/-- `cor:conditional`, paper/paper.tex: the full
physical coefficient producer computes its square factor, initializes both
sign components and performs the eight exact integer factor steps. -/
def prepareCoefficient : St VV MM :=
  .seq prepareSideSquare (.seq (.op (.copy coefficientPositive v1))
    (.seq (.op (.zero coefficientNegative)) (coefficientLoop (List.finRange 8))))

/-- `cor:conditional`, paper/paper.tex: the actual
coefficient producer uses only these independent binary scratch variables. -/
def coefficientPrepareScratch : List (Fin VV) := gammaSideSquare :: coefficientLoopScratch

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one finite ordinary program physically computes the exact
ORIGINAL signed eight-slot coefficient in two natural registers. -/
theorem prepareCoefficient_run (C : Ctx) (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM) (hc : Cst a)
    (hQ : a.env (requestFieldRegister 2) = request.parameters.Q)
    (hside : a.env gammaSide = request.parameters.N)
    (hd : ∀ slot, a.env (gammaDigit slot) = (choice slot).val)
    (hwidth : Cycle.seedLength request.parameters + 1 ≤ C.Wd) :
    Hs C prepareCoefficient a 129 (fun b =>
      b.env coefficientPositive = (originalCoefficientPair request choice).positive ∧
      b.env coefficientNegative = (originalCoefficientPair request choice).negative ∧
      Same a b ∧ Cst b ∧ Fr a b coefficientPrepareScratch) := by
  unfold prepareCoefficient
  refine Hs.seq (t1 := 3) (t2 := 125)
    (prepareSideSquare_run C request a hc hside hwidth) ?_
  intro b ⟨bN, bs, bc, bf⟩
  have hbf : Fr a b coefficientPrepareScratch := bf.weaken (by simp [coefficientPrepareScratch,
    coefficientLoopScratch, coefficientScratch])
  refine Hs.seq (t1 := 1) (t2 := 123) (hs_copy C coefficientPositive v1 b (by decide)) ?_
  intro c hcstate
  subst hcstate
  refine Hs.seq (t1 := 1) (t2 := 121) (hs_zero C coefficientNegative _) ?_
  intro d hdstate
  subst hdstate
  let d := (b.set coefficientPositive (b.env v1)).set coefficientNegative 0
  have df : Fr b d coefficientPrepareScratch :=
    (Fr.set b _ (by simp [coefficientPrepareScratch, coefficientLoopScratch, coefficientScratch])).trans
      (Fr.set _ _ (by simp [coefficientPrepareScratch, coefficientLoopScratch, coefficientScratch]))
  have dc : Cst d := Cst.of_fr bc df (by decide)
  have dQ : d.env (requestFieldRegister 2) = request.parameters.Q := by
    rw [df _ (by decide), bf _ (by decide)]
    exact hQ
  have dN : d.env gammaSideSquare = request.parameters.N ^ 2 := by
    vsimp [d, bN]
  have dd : ∀ slot, d.env (gammaDigit slot) = (choice slot).val := by
    intro slot
    rw [df _ (by fin_cases slot <;> decide), bf _ (by fin_cases slot <;> decide)]
    exact hd slot
  refine Hs.mono (coefficientLoop_run C request choice (List.finRange 8) d dc ⟨1, 0⟩ 0
    (by vsimp [d, bc.one]) (by simp [d]) dQ dN dd (by simp) (by simp) hwidth) (by simp) ?_
  intro e ⟨ep, en, es, ec, ef⟩
  exact ⟨ep, en, bs.trans (((Same.set _ _ _).trans (Same.set _ _ _)).trans es), ec,
    hbf.trans (df.trans (ef.weaken (fun x hx => List.mem_cons_of_mem _ hx)))⟩

end NearQuarticWires.StageGamma
