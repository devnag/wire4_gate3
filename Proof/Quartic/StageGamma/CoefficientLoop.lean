import Proof.Quartic.StageGamma.PairNegative

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the finite
eight-factor integer product is implemented by exact natural-pair steps. -/
def coefficientLoop : List (Fin 8) → St VV MM
  | [] => skipS
  | slot :: slots => .seq (coefficientStep slot) (coefficientLoop slots)

/-- `cor:conditional`, paper/paper.tex: all actual
coefficient-loop changes are confined to binary arithmetic scratch. -/
def coefficientLoopScratch : List (Fin VV) := coefficientScratch ++ [vJ]

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the actual finite signed product computes every partial
coefficient exactly, with overflow bounds derived from the ORIGINAL bank
degree and no assumption on signs or zero factors. -/
theorem coefficientLoop_run (C : Ctx) (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (slots : List (Fin 8))
    (a : DS VV MM) (hc : Cst a) (p : CoefficientPair) (k : ℕ)
    (hp : a.env coefficientPositive = p.positive) (hn : a.env coefficientNegative = p.negative)
    (hQ : a.env (requestFieldRegister 2) = request.parameters.Q)
    (hN : a.env gammaSideSquare = request.parameters.N ^ 2)
    (hd : ∀ slot, a.env (gammaDigit slot) = (choice slot).val)
    (hmass : p.positive + p.negative ≤ 2 ^ (request.parameters.ell * k))
    (hcount : k + slots.length ≤ 8)
    (hwidth : Cycle.seedLength request.parameters + 1 ≤ C.Wd) :
    Hs C (coefficientLoop slots) a (15 * slots.length + 1) (fun b =>
      b.env coefficientPositive =
        (coefficientPairFold request.parameters.N request.parameters.Q choice slots p).positive ∧
      b.env coefficientNegative =
        (coefficientPairFold request.parameters.N request.parameters.Q choice slots p).negative ∧
      Same a b ∧ Cst b ∧ Fr a b coefficientLoopScratch) := by
  induction slots generalizing a p k with
  | nil =>
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hp,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hn, Same.set _ _ _,
      Cst.of_fr (T := [vJ]) hc (Fr.set a 0 (by simp)) (by decide),
      Fr.set a _ (by simp [coefficientLoopScratch])⟩
  | cons slot slots ih =>
    have hfit : 2 ^ (request.parameters.ell * k) * 2 ^ request.parameters.ell < 2 ^ C.Wd := by
      rw [← pow_add]
      apply Nat.pow_lt_pow_right (by decide)
      have hk : k + 1 ≤ 8 := by simp only [List.length_cons] at hcount; omega
      have hm := Nat.mul_le_mul_left request.parameters.ell hk
      dsimp [Cycle.seedLength] at hwidth
      nlinarith
    refine Hs.mono (Hs.seq (t1 := 14) (t2 := 15 * slots.length + 1)
      (coefficientStep_run C request slot (choice slot) a hc p
        (2 ^ (request.parameters.ell * k)) hp hn hQ hN (hd slot) hmass hfit) ?_)
      (by simp; omega) (fun _ h => h)
    intro b ⟨bp, bn, bs, bc, bf⟩
    let next := p.step request.parameters.N request.parameters.Q (choice slot).val
    have bm : next.positive + next.negative ≤ 2 ^ (request.parameters.ell * (k + 1)) := by
      rw [CoefficientPair.step_mass]
      have hh := Nat.mul_le_mul hmass (choiceCoefficient_abs_le request (choice slot))
      simpa only [← pow_add, Nat.mul_add, Nat.mul_one] using hh
    have bQ : b.env (requestFieldRegister 2) = request.parameters.Q := by
      rw [bf _ (by decide)]
      exact hQ
    have bN : b.env gammaSideSquare = request.parameters.N ^ 2 := by
      rw [bf _ (by decide)]
      exact hN
    have bd : ∀ i, b.env (gammaDigit i) = (choice i).val := by
      intro i
      rw [bf _ (by fin_cases i <;> decide)]
      exact hd i
    refine Hs.mono (ih b bc next (k + 1) bp bn bQ bN bd bm
      (by simp only [List.length_cons] at hcount; omega)) le_rfl ?_
    intro e ⟨ep, en, es, ec, ef⟩
    refine ⟨?_, ?_, bs.trans es, ec,
      (bf.weaken (fun x hx => List.mem_append_left _ hx)).trans ef⟩
    · simpa only [coefficientPairFold, List.foldl_cons] using ep
    · simpa only [coefficientPairFold, List.foldl_cons] using en

end NearQuarticWires.StageGamma
