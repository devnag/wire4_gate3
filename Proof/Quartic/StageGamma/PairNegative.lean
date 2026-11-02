import Proof.Quartic.StageGamma.PairMultiply

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: a negative
slot exchanges the two actual binary sign components after scaling. -/
def swapCoefficientPair : St VV MM :=
  .seq (.op (.copy coefficientTempPositive coefficientPositive))
    (.seq (.op (.copy coefficientPositive coefficientNegative))
      (.op (.copy coefficientNegative coefficientTempPositive)))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: an actual finite copy sequence negates the signed natural
pair without introducing a sign oracle or losing negative coefficients. -/
theorem swapCoefficientPair_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (p n : ℕ) (hp : a.env coefficientPositive = p) (hn : a.env coefficientNegative = n) :
    Hs C swapCoefficientPair a 5 (fun b =>
      b.env coefficientPositive = n ∧ b.env coefficientNegative = p ∧
      Same a b ∧ Cst b ∧ Fr a b coefficientScratch) := by
  unfold swapCoefficientPair
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_copy C coefficientTempPositive coefficientPositive a (by decide)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_copy C coefficientPositive coefficientNegative _ (by decide)) ?_
  intro b hb
  subst hb
  refine Hs.mono (hs_copy C coefficientNegative coefficientTempPositive _ (by decide)) le_rfl ?_
  rintro b rfl
  exact ⟨by vsimp [hn], by vsimp [hp],
    (Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _)),
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩,
    (Fr.set _ _ (by simp [coefficientScratch])).trans
      ((Fr.set _ _ (by simp [coefficientScratch])).trans
        (Fr.set _ _ (by simp [coefficientScratch])))⟩

/-- `cor:conditional`, paper/paper.tex: the actual
negative coefficient factor scales and exchanges the two binary registers. -/
def multiplyPairNegative (factor : Fin VV) : St VV MM :=
  .seq (multiplyPairPositive factor) swapCoefficientPair

/-- `cor:conditional` and `prop:time`, paper/paper.tex: a negative sample factor is implemented by real binary
multiplication and exact register exchange, at constant source cost. -/
theorem multiplyPairNegative_run (C : Ctx) (factor : Fin VV)
    (hfactor : factor ∉ coefficientScratch) (a : DS VV MM) (hc : Cst a)
    (p : CoefficientPair) (f : ℕ)
    (hp : a.env coefficientPositive = p.positive)
    (hn : a.env coefficientNegative = p.negative) (hf : a.env factor = f)
    (hpf : p.positive * f < 2 ^ C.Wd) (hnf : p.negative * f < 2 ^ C.Wd) :
    Hs C (multiplyPairNegative factor) a 13 (fun b =>
      b.env coefficientPositive = p.negative * f ∧
      b.env coefficientNegative = p.positive * f ∧ Same a b ∧ Cst b ∧
      Fr a b coefficientScratch) := by
  refine Hs.seq (t1 := 7) (t2 := 5)
    (multiplyPairPositive_run C factor hfactor a hc p f hp hn hf hpf hnf) ?_
  intro b ⟨bp, bn, bs, bc, bf⟩
  refine Hs.mono (swapCoefficientPair_run C b bc _ _ bp bn) le_rfl ?_
  intro e ⟨ep, en, es, ec, ef⟩
  exact ⟨ep, en, bs.trans es, ec, bf.trans ef⟩

/-- `cor:conditional`, paper/paper.tex: the original
sample factor N² is cached once in an independent binary variable. -/
def gammaSideSquare : Fin VV := ⟨92, by decide⟩

/-- `cor:conditional`, paper/paper.tex: an actual
radix-zero test selects Q or the negative N² coefficient. -/
def coefficientStep (slot : Fin 8) : St VV MM :=
  .ite (.eq (gammaDigit slot) vZ)
    (multiplyPairPositive (requestFieldRegister 2)) (multiplyPairNegative gammaSideSquare)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the exact ORIGINAL signed one-slot coefficient is computed
by ordinary arithmetic, with all products bounded by the original degree. -/
theorem coefficientStep_run (C : Ctx) (request : Machine.GammaRequest)
    (slot : Fin 8) (digit : Fin (request.parameters.Q + 1))
    (a : DS VV MM) (hc : Cst a) (p : CoefficientPair) (bound : ℕ)
    (hp : a.env coefficientPositive = p.positive) (hn : a.env coefficientNegative = p.negative)
    (hQ : a.env (requestFieldRegister 2) = request.parameters.Q)
    (hN : a.env gammaSideSquare = request.parameters.N ^ 2)
    (hd : a.env (gammaDigit slot) = digit.val)
    (hpair : p.positive + p.negative ≤ bound)
    (hfit : bound * 2 ^ request.parameters.ell < 2 ^ C.Wd) :
    Hs C (coefficientStep slot) a 14 (fun b =>
      b.env coefficientPositive = (p.step request.parameters.N request.parameters.Q digit.val).positive ∧
      b.env coefficientNegative = (p.step request.parameters.N request.parameters.Q digit.val).negative ∧
      Same a b ∧ Cst b ∧ Fr a b coefficientScratch) := by
  have hq := request.parameters.Q_le
  have hns : request.parameters.N ^ 2 ≤ 2 ^ request.parameters.ell := by
    change (2 ^ request.parameters.kh) ^ 2 ≤ _
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by have := request.parameters.k_le; omega)
  have productFit : ∀ f ≤ 2 ^ request.parameters.ell,
      p.positive * f < 2 ^ C.Wd ∧ p.negative * f < 2 ^ C.Wd := by
    intro f hf
    exact ⟨(Nat.mul_le_mul (by omega) hf).trans_lt hfit,
      (Nat.mul_le_mul (by omega) hf).trans_lt hfit⟩
  unfold coefficientStep
  refine Hs.ite (c := .eq (gammaDigit slot) vZ) (t := 13)
    (by change gammaDigit slot ≠ vZ; fin_cases slot <;> decide) ?_ ?_
  · intro he
    have hz : digit.val = 0 := by
      have hh : a.env (gammaDigit slot) = a.env vZ := of_decide_eq_true he
      rwa [hd, hc.z] at hh
    refine Hs.mono (multiplyPairPositive_run C (requestFieldRegister 2) (by decide)
      a hc p request.parameters.Q hp hn hQ (productFit _ hq).1 (productFit _ hq).2)
      (by omega) ?_
    intro b hb
    simpa [CoefficientPair.step, hz] using hb
  · intro he
    have hz : digit.val ≠ 0 := by
      have hh : a.env (gammaDigit slot) ≠ a.env vZ := of_decide_eq_false he
      rwa [hd, hc.z] at hh
    refine Hs.mono (multiplyPairNegative_run C gammaSideSquare (by decide)
      a hc p (request.parameters.N ^ 2) hp hn hN
      (productFit _ hns).1 (productFit _ hns).2) le_rfl ?_
    intro b hb
    simpa [CoefficientPair.step, hz] using hb

end NearQuarticWires.StageGamma
