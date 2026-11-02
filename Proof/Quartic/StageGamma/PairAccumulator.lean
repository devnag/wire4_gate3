import Proof.Quartic.StageGamma.ScaledTerm

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open scoped BigOperators
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: every
ORIGINAL coefficient address has its exact signed natural-pair term. -/
noncomputable def indexedTermPair (request : Machine.GammaRequest) (i : ℕ) : CoefficientPair :=
  if h : i < (request.parameters.Q + 1) ^ 8 then
    originalTermPair request (littleChoiceEquiv request.parameters.Q ⟨i, h⟩)
  else ⟨0, 0⟩

/-- `cor:conditional`, paper/paper.tex: the exact
partial accumulator consists of two uncancelled sums over actual addresses. -/
noncomputable def originalPartialPair (request : Machine.GammaRequest) (k : ℕ) : CoefficientPair :=
  ⟨∑ i ∈ Finset.range k, (indexedTermPair request i).positive,
    ∑ i ∈ Finset.range k, (indexedTermPair request i).negative⟩

/-- `prop:time`, paper/paper.tex: each ORIGINAL
addressed term has an unconditional uncancelled two-register bound. -/
theorem indexedTermPair_mass_le (request : Machine.GammaRequest) (i : ℕ) :
    (indexedTermPair request i).positive + (indexedTermPair request i).negative ≤
      2 ^ (2 * Cycle.seedLength request.parameters) := by
  unfold indexedTermPair
  split_ifs
  · exact originalTermPair_mass_le _ _
  · exact Nat.zero_le _

/-- `prop:time`, paper/paper.tex: even the
uncancelled positive and negative accumulator registers together have
only O(S) bits throughout the exact ORIGINAL `(Q+1)^8` census. -/
theorem originalPartialPair_mass_le (request : Machine.GammaRequest) (k : ℕ)
    (hk : k ≤ (request.parameters.Q + 1) ^ 8) :
    (originalPartialPair request k).positive + (originalPartialPair request k).negative ≤
      2 ^ (3 * Cycle.seedLength request.parameters + 8) := by
  dsimp only [originalPartialPair]
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _i ∈ Finset.range k, 2 ^ (2 * Cycle.seedLength request.parameters) :=
      Finset.sum_le_sum (fun i _ => indexedTermPair_mass_le request i)
    _ = k * 2 ^ (2 * Cycle.seedLength request.parameters) := by simp
    _ ≤ 2 ^ (Cycle.seedLength request.parameters + 8) *
        2 ^ (2 * Cycle.seedLength request.parameters) :=
      Nat.mul_le_mul_right _ (hk.trans (choiceCount_le request))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- `cor:conditional`, paper/paper.tex: one
enumeration step appends exactly its true indexed term to both components. -/
theorem originalPartialPair_succ (request : Machine.GammaRequest) (k : ℕ) :
    originalPartialPair request (k + 1) =
      ⟨(originalPartialPair request k).positive + (indexedTermPair request k).positive,
        (originalPartialPair request k).negative + (indexedTermPair request k).negative⟩ := by
  simp [originalPartialPair, Finset.sum_range_succ]

/-- `cor:conditional`, paper/paper.tex: actual
positive and negative accumulated contributions use two independent
binary registers, preserving every exact negative summand. -/
def gammaPositiveSum : Fin VV := ⟨100, by decide⟩
def gammaNegativeSum : Fin VV := ⟨101, by decide⟩

/-- `cor:conditional`, paper/paper.tex: one actual
accumulator step performs both signed-component binary additions. -/
def accumulatePair : St VV MM :=
  .seq (.op (.add gammaPositiveSum coefficientPositive))
    (.op (.add gammaNegativeSum coefficientNegative))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: actual accumulator additions have every overflow bound
discharged from the ORIGINAL choice census; signed cancellation is unused. -/
theorem accumulatePair_run (C : Ctx) (request : Machine.GammaRequest) (k : ℕ)
    (hk : k < (request.parameters.Q + 1) ^ 8) (a : DS VV MM) (hc : Cst a)
    (hp : a.env gammaPositiveSum = (originalPartialPair request k).positive)
    (hn : a.env gammaNegativeSum = (originalPartialPair request k).negative)
    (htp : a.env coefficientPositive = (indexedTermPair request k).positive)
    (htn : a.env coefficientNegative = (indexedTermPair request k).negative)
    (hwidth : 3 * Cycle.seedLength request.parameters + 9 ≤ C.Wd) :
    Hs C accumulatePair a 3 (fun b =>
      b.env gammaPositiveSum = (originalPartialPair request (k + 1)).positive ∧
      b.env gammaNegativeSum = (originalPartialPair request (k + 1)).negative ∧
      Same a b ∧ Cst b ∧ Fr a b [gammaPositiveSum, gammaNegativeSum]) := by
  have hm := originalPartialPair_mass_le request (k + 1) (by omega)
  have hs := originalPartialPair_succ request k
  have hpow : 2 ^ (3 * Cycle.seedLength request.parameters + 8) < 2 ^ C.Wd :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hpf : a.env gammaPositiveSum + a.env coefficientPositive < 2 ^ C.Wd := by
    rw [hp, htp]
    rw [hs] at hm
    dsimp only at hm
    omega
  have hnf : a.env gammaNegativeSum + a.env coefficientNegative < 2 ^ C.Wd := by
    rw [hn, htn]
    rw [hs] at hm
    dsimp only at hm
    omega
  unfold accumulatePair
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_add C gammaPositiveSum coefficientPositive a (by decide) hpf) ?_
  intro b hb
  subst hb
  refine Hs.mono (hs_add C gammaNegativeSum coefficientNegative _ (by decide)
    (by vsimp []; exact hnf)) le_rfl ?_
  rintro b rfl
  rw [hs]
  exact ⟨by vsimp [hp, htp], by vsimp [hn, htn],
    (Same.set _ _ _).trans (Same.set _ _ _),
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩,
    (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageGamma
