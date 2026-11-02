import Proof.Quartic.StageGamma.Metadata

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5

/-- `prop:time`, paper/paper.tex: the concrete
finite serializer has a fixed numerical control constant. -/
theorem gammaBankWriter_clockFactor_le : gammaBankWriter.clockFactor ≤ 100000 := by
  decide

/-- `cor:conditional`, paper/paper.tex: the complete
physical writer reads only ORIGINAL scalar fields, the cached modulus,
true radix digits, selected labels and actual packed walk cells. -/
theorem gammaBankWriter_params : ∀ x : Fin VV, x ∈ gammaBankWriter.params →
    x ∈ [requestFieldRegister 0, requestFieldRegister 3, requestFieldRegister 4,
      gammaModulus, gammaRest, gammaCellWidth, vZ, v1] ∨
    ∃ slot : Fin 8, x = gammaDigit slot ∨ x = gammaLabel slot ∨ x = gammaCell slot := by
  decide

/-- `cor:conditional`, paper/paper.tex: every actual
source variable used by the compact Gaussian input producer fits within
one more than the ORIGINAL seed's binary width. No child label is assumed. -/
theorem gammaBankWriter_params_fit (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM)
    (hc : Cst a) (ha : BankReady request choice a) (width : ℕ)
    (hwidth : Cycle.seedLength request.parameters + 1 ≤ width) :
    ∀ x ∈ gammaBankWriter.params, a.env x < 2 ^ width := by
  let S := Cycle.seedLength request.parameters
  have hell : request.parameters.ell + 1 ≤ S + 1 := by dsimp [S, Cycle.seedLength]; omega
  have hpow : 2 ^ (request.parameters.ell + 1) ≤ 2 ^ width :=
    Nat.pow_le_pow_right (by decide) (hell.trans hwidth)
  have hSl : S < 2 ^ width := by
    have hh : S < 2 ^ S := Nat.lt_two_pow_self
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hmod : request.parameters.modulus < 2 ^ (request.parameters.ell + 1) :=
    request.parameters.cert.2.1.2
  have hdigit : ∀ slot, (choice slot).val < 2 ^ (request.parameters.ell + 1) := by
    intro slot
    have hh := (choice slot).isLt
    have hq := request.parameters.Q_le
    have he : 1 ≤ 2 ^ request.parameters.ell := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  have hk : 2 * request.parameters.kh ≤ S := by
    have hh := request.parameters.k_le
    dsimp [S, Cycle.seedLength]
    omega
  intro x hx
  rcases gammaBankWriter_params x hx with hscalar | ⟨slot, hd | hl | hcell⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hscalar
    rcases hscalar with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ha.ell]
      exact (lt_of_le_of_lt (by dsimp [S, Cycle.seedLength]; omega) hSl)
    · rw [ha.plen]
      exact lt_of_le_of_lt request.prefixFits hSl
    · rw [ha.pre]
      exact request.prefixCodeFits.trans_le (Nat.pow_le_pow_right (by decide)
        (request.prefixFits.trans (by omega)))
    · rw [ha.modulus]
      exact hmod.trans_le hpow
    · rw [ha.rest]
      exact (lt_of_le_of_lt (Nat.sub_le _ _) hSl)
    · rw [ha.cellWidth]
      exact (lt_of_le_of_lt hk hSl)
    · rw [hc.z]
      exact Nat.two_pow_pos _
    · rw [hc.one]
      exact Nat.one_lt_two_pow (by have := request.parameters.one_le_ell; dsimp [Cycle.seedLength] at hwidth; omega)
  · subst hd
    rw [ha.digit]
    exact (hdigit slot).trans_le hpow
  · subst hl
    rw [ha.label]
    exact (lt_of_le_of_lt (Nat.sub_le _ _) (hdigit slot)).trans_le hpow
  · subst hcell
    rw [ha.cell]
    have hh := Cycle.gammaChoiceCons_bounds
    have hv : Sampler.cellNum request.parameters (Cycle.edge (by norm_num) request.walk slot) <
        2 ^ (2 * request.parameters.kh) := Sampler.ofVec_lt _
    exact hv.trans_le (Nat.pow_le_pow_right (by decide) (hk.trans (by omega)))

/-- `prop:time`, paper/paper.tex: the complete
compact source writer is paid by a concrete linear seed factor. -/
theorem gammaBankWriter_cost_le_numeric (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM)
    (ha : BankReady request choice a) :
    gammaBankWriter.cost a ≤ 100000 * (Cycle.seedLength request.parameters + 1) :=
  (gammaBankWriter_cost_le request a ha.ell ha.plen ha.cellWidth ha.rest).trans
    (Nat.mul_le_mul_right _ gammaBankWriter_clockFactor_le)

end NearQuarticWires.StageGamma
