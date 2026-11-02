import Proof.Quartic.Program.Stages
import Proof.Quartic.Cells.ParametersRationalBounds
import Proof.Quartic.Cells.ParametersPreparationWords

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- The complete literal parameter record of `sec:params` has
polynomial serialized length at the input precision, `prop:time`,
paper/paper.tex. Every stored field and
both finite lists are included in the actual `parametersWord`. -/
theorem parametersWord_preparation_bound (hs : ParameterRules x p) (B1 L : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num.natAbs ≤ 2 ^ L) (hden : x.beta.den ≤ 2 ^ L) :
    (Program.parametersWord p).length ≤
      100 * (preparationEnvelope B1 x.n + L + (x.n + 1) ^ 2 + 2) := by
  let V := preparationEnvelope B1 x.n
  let B := V + L
  have hscl := hs.scalar_preparation_bounds B1 hb
  have hv : V ≤ 2 ^ B := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right V L))
  have hn (v : ℕ) (h : v ≤ V) : (natWord v).length ≤ 2 * B + 3 :=
    natWord_length_of_power_bound v B (h.trans hv)
  have h_lambda := hn p.lambda hscl.lambda
  have h_mu := hn p.mu hscl.mu
  have h_m := hn p.m hscl.m
  have h_r := hn p.r hscl.r
  have h_s := hn p.s hscl.s
  have h_b := hn p.b hscl.b
  have h_k := hn p.k hscl.k
  have h_Jmax := hn p.Jmax hscl.Jmax
  have h_T := hn p.T hscl.T
  have h_tau := hn p.tau hscl.tau
  have h_U := hn p.U hscl.U
  have h_Xmax := hn p.Xmax hscl.Xmax
  have h_dstar := hn p.dstar hscl.dstar
  have h_omega1 := hn p.omega1 hscl.omega1
  have h_omega2 := hn p.omega2 hscl.omega2
  have h_MF := hn p.MF hscl.MF
  have h_ellf := hn p.ellf hscl.ellf
  have h_S := hn p.S hscl.S
  have h_NatAtoms := hn p.NatAtoms hscl.NatAtoms
  have h_childCap := hn p.childCap hscl.childCap
  have h_Uocc := hn p.Uocc hscl.Uocc
  have h_Dmax := hn p.Dmax hscl.Dmax
  have h_BN := hn p.BN hscl.BN
  have h_P := hn p.P hscl.P
  have h_e := hn p.e hscl.e
  have h_hE := hn p.hE hscl.hE
  have h_h := hn p.h hscl.h
  have h_Lw := hn p.Lw hscl.Lw
  have h_Qexp := hn p.Qexp hscl.Qexp
  have h_Dprime := hn p.Dprime hscl.Dprime
  have h_L2 := hn p.L2 hscl.L2
  have h_M1 := hn p.M1 hscl.M1
  have h_J := hn p.J hscl.J
  have h_A := hn p.A hscl.A
  have h_Lambda := hn p.Lambda hscl.Lambda
  have h_N : (natWord p.N).length ≤ 2 * B + 3 := by
    apply natWord_length_of_power_bound
    rw [hs.N_eq]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.div_le_self p.k 2).trans (hscl.k.trans (Nat.le_add_right V L)))
  have h_Q : (natWord p.Q).length ≤ 2 * B + 3 := by
    apply natWord_length_of_power_bound
    rw [hs.Q_eq]
    exact Nat.pow_le_pow_right (by norm_num) (hscl.Qexp.trans (Nat.le_add_right V L))
  have hrat := hs.rational_preparation_bounds B1 L hb hnum hden
  have h_pi := ratWord_length_of_power_bounds p.pi0 B hrat.1.1 hrat.1.2
  have h_eta := ratWord_length_of_power_bounds p.eta B hrat.2.1.1 hrat.2.1.2
  have h_ell := ratWord_length_of_power_bounds p.ell0 B hrat.2.2.1 hrat.2.2.2
  have h_factors := hs.factor_word_preparation_bound
  have h_primes := hs.prime_word_preparation_bound
  simp only [Program.parametersWord, List.length_append]
  dsimp only [B, V] at *
  omega

end NearQuarticWires.Cells.ParameterRules
