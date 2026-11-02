import Proof.Quartic.Cycle.ConditionalGamma

set_option autoImplicit false

namespace NearQuarticWires.Cycle
attribute [local instance] Classical.propDecidable
open Finset

/-- Paper `cor:conditional`: exactly (Q+1)^8 choices, zero for the constant Q. -/
abbrev GammaChoice (Q : ℕ) := Fin 8 → Fin (Q + 1)

/-- Paper `cor:conditional`: the selected sample label, or the constant term. -/
def sampleChoice {Q : ℕ} (a : Fin (Q+1)) : Option (Fin Q) := Fin.cases none some a

/-- Paper `cor:conditional`: the INTEGER coefficient of one expansion slot. -/
def choiceCoefficient (N Q : ℕ) (a : Fin (Q+1)) : ℤ :=
  Fin.cases (Q : ℤ) (fun _ => -(N : ℤ)^2) a

/-- Paper `cor:conditional`: the event selected in one walk slot. -/
def choiceMatches {N Q : ℕ} (S : Fin Q → NearQuarticWires.Sampler.Cell N)
    (c : NearQuarticWires.Sampler.Cell N) (a : Fin (Q+1)) : Prop :=
  match sampleChoice a with
  | none => True
  | some j => S j = c

/-- Paper `cor:conditional`: the signed coefficient of one of the (Q+1)^8 products. -/
def gammaChoiceWeight (N Q : ℕ) (α : GammaChoice Q) : ℤ :=
  ∏ l, choiceCoefficient N Q (α l)

/-- Paper `cor:conditional`: exact one-slot Γ expansion. -/
theorem gammaInt_choice_sum {N Q : ℕ}
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (c : NearQuarticWires.Sampler.Cell N) :
    gammaInt S c = ∑ a : Fin (Q+1), choiceCoefficient N Q a *
      (if choiceMatches S c a then 1 else 0) := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [choiceCoefficient, choiceMatches, sampleChoice, Fin.cases_zero,
    Fin.cases_succ, if_true, mul_one]
  unfold gammaInt
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Paper `cor:conditional`: the concrete signed Γ_w has exactly (Q+1)^8 expansion terms. -/
theorem walkGammaInt_choice_sum {N Q : ℕ}
    (S : Fin Q → NearQuarticWires.Sampler.Cell N) (w : Walk N 4) :
    walkGammaInt (by norm_num) S w =
      ∑ α : GammaChoice Q, gammaChoiceWeight N Q α *
        (if ∀ l, choiceMatches S (edge (by norm_num) w l) (α l) then 1 else 0) := by
  classical
  unfold walkGammaInt
  simp_rw [gammaInt_choice_sum]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.prod_mul_distrib]
  change (gammaChoiceWeight N Q α) *
      (∏ l, if choiceMatches S (edge (by norm_num) w l) (α l) then (1 : ℤ) else 0) = _
  congr 1
  simp [Finset.prod_boole]

/-- Paper `cor:conditional`: no padded field-label enumeration is counted. -/
theorem card_gammaChoice (Q : ℕ) : Fintype.card (GammaChoice Q) = (Q+1)^8 := by
  simp [GammaChoice]

end NearQuarticWires.Cycle
