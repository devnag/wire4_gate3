import Proof.Quartic.StagePrep.CanonicalCases
import Proof.Quartic.Cells.ParametersSelectedCost

/-!
# The canonical preparation clock on every guard outcome

Paper: `sec:params`, paper/paper.tex, and
the preparation cost in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open Cells.ParameterArithmetic

/-- A fixed original-input envelope for all canonical paths
in `prop:time`, paper/paper.tex. -/
def canonicalBudgetMajorant (B1 L : ℕ) : ℕ :=
  (publicScalesCostCoefficient B1+100000*(32*B1+2203)^4+
    10*(preparationCoefficient B1+33*B1+4000)+1000)*(L+1)^(2*B1+12)

/-- Every canonical preparation charge in `prop:time`,
paper/paper.tex, is polynomial in the original
input length, including initial rejection and all later failures. -/
theorem canonicalPreparationBudget_le (x : Cells.ParameterInput)
    (hv : ValidInput x) (B1 L num den : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta*(x.n:ℚ)^B1)
    (hnum : x.beta.num=num) (hden : x.beta.den=den)
    (hnumBits : num ≤ 2^L) (hdenBits : den ≤ 2^L) :
    canonicalPreparationBudget x num den ≤ canonicalBudgetMajorant B1 L := by
  have hu : 0<num := by
    have h := Rat.num_pos.mpr hv.2.2.2.2.1
    rw [hnum] at h
    exact_mod_cast h
  have hd : 0<den := by rw [←hden]; exact x.beta.den_pos
  have hR : 1 ≤ (L+1)^(2*B1+12) := Nat.one_le_pow _ _ (by omega)
  unfold canonicalPreparationBudget
  split
  · rename_i hr
    let p := attemptPublicParameters x (Cells.publicScales x)
    have hs : AttemptRules x p :=
      attemptPublicParameters_rules x (Cells.publicScales x) (Cells.publicScales_core x hv hr)
    have hP : p.P ≤ x.n := by rw [hs.P_eq]; exact Nat.findGreatest_le _
    have hD : p.Dprime ≤ (x.n+1)^2 := by
      rw [hs.Dprime_eq,hs.primes_eq]
      exact (scan_windows_le_arity_square x.n p.P hP x.pair).1
    have hh : p.h ≤ x.n := by
      rw [hs.h_eq,hs.hE_eq]
      exact (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hP)
    have hcost := hs.toCoreRules.selectedPreparationCost_preparation_bound
      B1 L num den hn hb hnum hden hu hd hnumBits hdenBits hP hD hh
    exact hcost.trans (by unfold canonicalBudgetMajorant; nlinarith)
  · have hnR : x.n ≤ (L+1)^(2*B1+12) :=
      (hn.trans (Nat.le_succ _)).trans (Nat.le_self_pow (by omega) _)
    have hcoef : 1000 ≤ publicScalesCostCoefficient B1+100000*(32*B1+2203)^4+
        10*(preparationCoefficient B1+33*B1+4000)+1000 := by omega
    have hmul := Nat.mul_le_mul_right ((L+1)^(2*B1+12)) hcoef
    unfold canonicalBudgetMajorant
    nlinarith only [hnR,hR,hmul]

/-- The canonical original-input envelope of `prop:time`,
paper/paper.tex, is a fixed polynomial. -/
theorem canonicalBudgetMajorant_poly (B1 : ℕ) : PolyB (canonicalBudgetMajorant B1) := by
  unfold canonicalBudgetMajorant
  polyb

end NearQuarticWires.StagePrep
