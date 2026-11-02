import Proof.Quartic.StageGamma.GaussCount

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: one actual
signed term is a natural-pair coefficient multiplied by its exact ORIGINAL
prefix-restored Gaussian count. -/
noncomputable def originalTermPair (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : CoefficientPair :=
  let p := originalCoefficientPair request choice
  let count := originalScaledCount request choice
  ⟨p.positive * count, p.negative * count⟩

/-- `cor:conditional`, paper/paper.tex: the physical
natural-pair term represents precisely the original signed numerator term. -/
theorem originalTermPair_value (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (originalTermPair request choice).value =
      (2 : ℤ) ^ request.prefixLength * expansionTerm request choice := by
  rw [← scaledTerm_product]
  rw [← originalCoefficientPair_value, ← originalScaledCount_eq]
  dsimp [originalTermPair, CoefficientPair.value]
  ring

/-- `prop:time`, paper/paper.tex: the actual two
term registers are bounded before any cancellation, uniformly over every
ORIGINAL choice, arbitrary prefix and consistency case. -/
theorem originalTermPair_mass_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (originalTermPair request choice).positive + (originalTermPair request choice).negative ≤
      2 ^ (2 * Cycle.seedLength request.parameters) := by
  have hp := originalCoefficientPair_mass_le request choice
  have hc := originalScaledCount_le request choice
  dsimp only [originalTermPair]
  rw [← Nat.add_mul]
  calc
    _ ≤ 2 ^ Cycle.seedLength request.parameters * 2 ^ Cycle.seedLength request.parameters :=
      Nat.mul_le_mul hp hc
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- `cor:conditional`, paper/paper.tex: the actual
prefix-restored count is formed from the Gaussian reply, then physically
multiplied into both signed coefficient components. -/
def prepareScaledTerm : St VV MM :=
  .seq prepareGaussCount (multiplyPairPositive gammaCount)

/-- `cor:conditional`, paper/paper.tex: the entire
term producer changes only count and coefficient arithmetic workspace. -/
def scaledTermScratch : List (Fin VV) :=
  [gammaCount, gammaCountExponent, gammaCountIndex] ++ coefficientScratch

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one real finite program computes each complete ORIGINAL
signed term, including inconsistent systems and negative coefficients. -/
theorem prepareScaledTerm_run (C : Ctx) (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM) (hc : Cst a)
    (hp : a.env (requestFieldRegister 3) = request.prefixLength)
    (he : a.env gammaExponent = kernelExponent request choice)
    (hf : a.env gammaFlag = (kernelFlag request choice).toNat)
    (hpositive : a.env coefficientPositive = (originalCoefficientPair request choice).positive)
    (hnegative : a.env coefficientNegative = (originalCoefficientPair request choice).negative)
    (hwidth : 2 * Cycle.seedLength request.parameters + 1 ≤ C.Wd) :
    Hs C prepareScaledTerm a (5 * Cycle.seedLength request.parameters + 19) (fun b =>
      b.env coefficientPositive = (originalTermPair request choice).positive ∧
      b.env coefficientNegative = (originalTermPair request choice).negative ∧
      Same a b ∧ Cst b ∧ Fr a b scaledTermScratch) := by
  have hh := prepareGaussCount_run C request choice a hc hp he hf (by omega)
  refine Hs.seq (t1 := 5 * Cycle.seedLength request.parameters + 11) (t2 := 7) hh ?_
  intro b ⟨bcount, bs, bc, bf⟩
  have bp : b.env coefficientPositive = (originalCoefficientPair request choice).positive := by
    rw [bf _ (by decide)]
    exact hpositive
  have bn : b.env coefficientNegative = (originalCoefficientPair request choice).negative := by
    rw [bf _ (by decide)]
    exact hnegative
  have hmass := originalTermPair_mass_le request choice
  have hpow : 2 ^ (2 * Cycle.seedLength request.parameters) < 2 ^ C.Wd :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hpf : (originalCoefficientPair request choice).positive * originalScaledCount request choice <
      2 ^ C.Wd := by
    change (originalTermPair request choice).positive < _
    omega
  have hnf : (originalCoefficientPair request choice).negative * originalScaledCount request choice <
      2 ^ C.Wd := by
    change (originalTermPair request choice).negative < _
    omega
  refine Hs.mono (multiplyPairPositive_run C gammaCount (by decide) b bc
    (originalCoefficientPair request choice) (originalScaledCount request choice)
    bp bn bcount hpf hnf) le_rfl ?_
  intro e ⟨ep, en, es, ec, ef⟩
  exact ⟨ep, en, bs.trans es, ec,
    (bf.weaken (fun x hx => List.mem_append_left _ hx)).trans
      (ef.weaken (fun x hx => List.mem_append_right _ hx))⟩

end NearQuarticWires.StageGamma
