import Proof.Quartic.Cells.AsymptoticsPrime
import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params`, paper/paper.tex: the remaining finite
selection rules, expressed in terms of the initial public scales. -/
def finishSelection (x : ParameterInput) (s : Parameters) : Option Parameters :=
  if DegreePass x.n s.m s.k s.Uocc 0 then
    let Dmax := availableDegree x s
    let P := availablePrime x s
    if PrimeCandidate x.n s.BN s.Jmax s.m s.Xmax Dmax P then
      match liftExponent s.BN P with
      | none => none
      | some e =>
        if 4 * s.m * s.Xmax + 2 * s.m * s.k ≤ Dmax then
          let primes := NearCubicGates.Close.Counter.dyadicPrimes P
          if primes.Nonempty then
            let Dprime := NearCubicGates.ScalarWindow.window primes
            let L2 := NearCubicGates.Close.Counter.pairSide Dprime
            let Lw := NearCubicGates.Close.Counter.windowInUse x.pair L2 Dprime
            let hE := P / 4
            let h := hE / (2 * s.m)
            if 64 * s.T ≤ h then
              let ell0 : ℚ := (32 * s.m * s.U : ℕ)
              let ratio := NearCubicGates.Close.Counter.firstRatio ell0 h s.T
              match NearCubicGates.Close.Counter.stopIndex ratio x.n with
              | none => none
              | some Jlean =>
                let J := Jlean + 1
                if J ≤ s.Jmax then
                  let factors := NearCubicGates.Close.Counter.chainFactors ratio Jlean
                  let A := factors.prod
                  some { s with
                    Dmax := Dmax
                    P := P
                    e := e
                    primes := primes
                    Dprime := Dprime
                    L2 := L2
                    Lw := Lw
                    hE := hE
                    h := h
                    ell0 := ell0
                    M1 := NearCubicGates.Close.Counter.firstDen ell0 h s.T
                    J := J
                    factors := factors
                    A := A
                    Lambda := (Lw - 1) * A / 2 + 1 }
                else none
            else none
          else none
        else none
    else none
  else none

/-- `sec:params`, paper/paper.tex: after the initial
admission and geometry guards, the canonical computation is exactly the
remaining selection rules applied to its public scales. -/
theorem prepare_eq_finish (x : ParameterInput) (hv : ValidInput x)
    (hr : 4 * (16 * NearCubicGates.Target.mu x.n) ≤ x.n) :
    prepare x = finishSelection x (publicScales x) := by
  unfold prepare
  simp only [if_pos hv, if_pos hr]
  rfl

/-- `sec:params`, paper/paper.tex: Bertrand's postulate
ensures a prime in the actual dyadic prime set at every permitted scale. -/
theorem dyadicPrimes_nonempty (P : ℕ) (hP : 4 ≤ P) :
    (NearCubicGates.Close.Counter.dyadicPrimes P).Nonempty := by
  obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (P / 2) (by omega)
  refine ⟨q, (NearCubicGates.Close.Counter.mem_dyadicPrimes P q).mpr ⟨?_, hq, ?_⟩⟩
  · exact hhi.trans (Nat.mul_div_le P 2)
  · omega

/-- `sec:params`, paper/paper.tex: a passing degree
and prime choice, the moment-degree guard, and the height guard suffice for
successful completion; the prime-set and chain guards are derived. -/
theorem finishSelection_isSome (x : ParameterInput) (s : Parameters) (hs : CoreRules x s)
    (hd : DegreePass x.n s.m s.k s.Uocc 0)
    (hp : PrimeCandidate x.n s.BN s.Jmax s.m s.Xmax (availableDegree x s) (availablePrime x s))
    (hm : 4 * s.m * s.Xmax + 2 * s.m * s.k ≤ availableDegree x s)
    (hh : 64 * s.T ≤ (availablePrime x s / 4) / (2 * s.m)) :
    ∃ p, finishSelection x s = some p := by
  let P := availablePrime x s
  let h := (P / 4) / (2 * s.m)
  let ell0 : ℚ := (32 * s.m * s.U : ℕ)
  have hP4 : 4 ≤ P := by have := hp.1; omega
  obtain ⟨e, he⟩ := liftExponent_isSome s.BN P hP4
  have hpr : (NearCubicGates.Close.Counter.dyadicPrimes P).Nonempty := dyadicPrimes_nonempty P hP4
  dsimp only [P] at hpr
  have hn : h ≤ x.n := (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hp.2.1)
  have hsize : h ≤ x.n * s.T := hn.trans (Nat.le_mul_of_pos_right _ hs.T_pos)
  obtain ⟨j, hj⟩ := NearCubicGates.Close.Counter.stopIndex_exists s.T h x.n ell0 hs.T_pos hh hsize
  have hbound := (NearCubicGates.Close.Counter.leastUpTo_spec _ _ _ hj).2.1
  have hJ : j + 1 ≤ s.Jmax := by
    rw [hs.Jmax_eq, hs.mu_eq]
    unfold NearCubicGates.Close.Counter.Jmax at hbound
    omega
  unfold finishSelection
  simp only [if_pos hd, if_pos hp]
  change ∃ p, (match liftExponent s.BN P with
    | none => none
    | some f => _) = some p
  rw [he]
  simp only [if_pos hm, if_pos hpr, if_pos hh]
  change ∃ p, (match NearCubicGates.Close.Counter.stopIndex
    (NearCubicGates.Close.Counter.firstRatio ell0 h s.T) x.n with
    | none => none
    | some k => _) = some p
  rw [hj]
  simp only [if_pos hJ]
  exact ⟨_, rfl⟩

end NearQuarticWires.Cells
