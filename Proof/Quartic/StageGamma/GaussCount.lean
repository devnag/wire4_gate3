import Proof.Quartic.StageGamma.CoefficientPrepare
import Proof.Quartic.StageGamma.TermProduct

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the true
Gaussian flag and nullity determine the prefix-scaled ORIGINAL count. -/
noncomputable def originalScaledCount (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : ℕ :=
  if kernelFlag request choice then
    2 ^ (request.prefixLength + kernelExponent request choice) else 0

/-- `cor:conditional`, paper/paper.tex: the actual
nullity leaves at most the ORIGINAL seed length after prefix restoration. -/
theorem prefix_add_kernelExponent_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    request.prefixLength + kernelExponent request choice ≤ Cycle.seedLength request.parameters := by
  have hp := request.prefixFits
  dsimp [kernelExponent, Cycle.seedLength] at *
  omega

/-- `cor:conditional`, paper/paper.tex: no
completion sum is hidden in the decoded Gaussian count. -/
theorem originalScaledCount_eq (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (originalScaledCount request choice : ℤ) = scaledGaussCount request choice := by
  unfold originalScaledCount scaledGaussCount JoinElimination.condProbGauss
  dsimp only
  change ((if kernelFlag request choice then
    2 ^ (request.prefixLength + kernelExponent request choice) else 0 : ℕ) : ℤ) =
    (2 : ℤ) ^ request.prefixLength *
      ((if kernelFlag request choice then 2 ^ kernelExponent request choice else 0 : ℕ) : ℤ)
  cases kernelFlag request choice <;> simp [pow_add]

/-- `prop:time`, paper/paper.tex: restoring the
original prefix does not exceed one seed length of count bits. -/
theorem originalScaledCount_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    originalScaledCount request choice ≤ 2 ^ Cycle.seedLength request.parameters := by
  unfold originalScaledCount
  split_ifs
  · exact Nat.pow_le_pow_right (by decide) (prefix_add_kernelExponent_le request choice)
  · exact Nat.zero_le _

/-- `cor:conditional`, paper/paper.tex: the actual
binary count is stored separately from coefficient and accumulator registers. -/
def gammaCount : Fin VV := ⟨102, by decide⟩
def gammaCountExponent : Fin VV := ⟨103, by decide⟩
def gammaCountIndex : Fin VV := ⟨104, by decide⟩

/-- `cor:conditional`, paper/paper.tex: a consistent
system's count is formed by real binary exponentiation of prefix+nullity. -/
def prepareConsistentCount : St VV MM :=
  .seq (.op (.copy gammaCountExponent gammaExponent))
    (.seq (.op (.add gammaCountExponent (requestFieldRegister 3)))
      (binaryPower gammaCountIndex gammaCountExponent gammaCount))

/-- `cor:conditional`, paper/paper.tex: the exact
prefix-restored count is computed from the actual Gaussian consistency bit. -/
def prepareGaussCount : St VV MM :=
  .ite (.eq gammaFlag vZ) (.op (.zero gammaCount)) prepareConsistentCount

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the exact ORIGINAL scaled count is physically computed from
the decoded Gaussian reply, preserving every other request/source register. -/
theorem prepareGaussCount_run (C : Ctx) (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM) (hc : Cst a)
    (hp : a.env (requestFieldRegister 3) = request.prefixLength)
    (he : a.env gammaExponent = kernelExponent request choice)
    (hf : a.env gammaFlag = (kernelFlag request choice).toNat)
    (hwidth : Cycle.seedLength request.parameters + 1 ≤ C.Wd) :
    Hs C prepareGaussCount a (5 * Cycle.seedLength request.parameters + 11) (fun b =>
      b.env gammaCount = originalScaledCount request choice ∧ Same a b ∧ Cst b ∧
      Fr a b [gammaCount, gammaCountExponent, gammaCountIndex]) := by
  let T : List (Fin VV) := [gammaCount, gammaCountExponent, gammaCountIndex]
  have hconst : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T := by decide
  have hsum := prefix_add_kernelExponent_le request choice
  have hfit : kernelExponent request choice + request.prefixLength < 2 ^ C.Wd := by
    have hh : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    omega
  unfold prepareGaussCount
  refine Hs.ite (c := .eq gammaFlag vZ) (t := 5 * Cycle.seedLength request.parameters + 10)
    (by change gammaFlag ≠ vZ; decide) ?_ ?_
  · intro hz
    have hfalse : kernelFlag request choice = false := by
      revert hz
      simp only [Cnd.eval, hf, hc.z]
      cases kernelFlag request choice <;> simp
    refine Hs.mono (hs_zero C gammaCount a) (by omega) ?_
    rintro b rfl
    exact ⟨by simp [originalScaledCount, hfalse], Same.set _ _ _,
      Cst.of_fr hc (Fr.set a _ (by simp [T])) hconst,
      Fr.set a _ (by decide)⟩
  · intro hz
    have htrue : kernelFlag request choice = true := by
      revert hz
      simp only [Cnd.eval, hf, hc.z]
      cases kernelFlag request choice <;> simp
    unfold prepareConsistentCount
    refine Hs.mono (Hs.seq (t1 := 1)
      (t2 := 5 * (kernelExponent request choice + request.prefixLength) + 8)
      (hs_copy C gammaCountExponent gammaExponent a (by decide)) ?_)
      (by omega) (fun _ h => h)
    intro b hb
    subst hb
    refine Hs.mono (Hs.seq (t1 := 1)
      (t2 := 5 * (kernelExponent request choice + request.prefixLength) + 6)
      (hs_add C gammaCountExponent (requestFieldRegister 3)
        (a.set gammaCountExponent (a.env gammaExponent)) (by decide)
        (by
          rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), he, hp]
          exact hfit)) ?_) (by omega) (fun _ h => h)
    intro b hb
    subst hb
    let b := (a.set gammaCountExponent (a.env gammaExponent)).set gammaCountExponent
      ((a.set gammaCountExponent (a.env gammaExponent)).env gammaCountExponent +
        (a.set gammaCountExponent (a.env gammaExponent)).env (requestFieldRegister 3))
    have bf : Fr a b T := (Fr.set a _ (by simp [T])).trans (Fr.set _ _ (by simp [T]))
    have bc : Cst b := Cst.of_fr hc bf hconst
    refine Hs.mono (binaryPower_run C gammaCountIndex gammaCountExponent gammaCount
      (by decide) (by decide) (by decide) (by decide) b bc
      (kernelExponent request choice + request.prefixLength) (by vsimp [b, he, hp])
      (by omega)) le_rfl ?_
    intro e ⟨ecount, es, ec, ef⟩
    refine ⟨by simpa [originalScaledCount, htrue, Nat.add_comm] using ecount,
      ((Same.set _ _ _).trans (Same.set _ _ _)).trans es, ec,
      bf.trans (ef.weaken (by simp [T]))⟩

end NearQuarticWires.StageGamma
