import Statement
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# A checked comparison with the distance assertion in BCGT13 Lemma 11.10

BCGT13, ECCC TR12-045 revision 3, Lemma 11.10 Case 2, p.67, claims
distance at least `(2^η-1)/2^η` from the degree-`dKE κ η` Reed–Solomon
code after multiplying the selected polynomial by `X^(dKE κ η-d)`.
Over the field with sixteen elements, at `κ=4`, `η=2`, `d=0`, a monic
polynomial with six distinct roots gives distance `10/16`, below `3/4`.
This concerns that distance assertion, not Corollary 11.13's statement.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance

open Polynomial
open NearCubicGates.Published.BCGT13

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

noncomputable abbrev F16 := GaloisField 2 4

noncomputable instance : Fintype F16 := Fintype.ofFinite F16
noncomputable instance : DecidableEq F16 := Classical.decEq F16

theorem field_card : Fintype.card F16 = 16 := by
  have h:=GaloisField.card 2 4 (by decide)
  rw [Nat.card_eq_fintype_card] at h
  exact h

/-- The entire field is a four-dimensional binary vector space. -/
theorem field_binary_dimension : Module.finrank (ZMod 2) F16 = 4 :=
  GaloisField.finrank 2 (by decide)

noncomputable def evaluationSet : Finset F16 := Finset.univ

theorem evaluationSet_card : evaluationSet.card = 16 := by
  simpa only [evaluationSet,Finset.card_univ] using field_card

/-- The evaluation set is the entire binary subspace, with zero offset. -/
theorem evaluationSet_subspace :
    (evaluationSet : Set F16) = ((⊤ : Submodule (ZMod 2) F16) : Set F16) := by
  ext x
  simp [evaluationSet]

theorem printed_parameters : dKE 4 2 = 3 := by decide

private theorem exists_six_points : ∃T : Finset F16,T.card=6 := by
  have h : 6 ≤ (Finset.univ : Finset F16).card := by
    rw [Finset.card_univ,field_card]
    decide
  obtain ⟨T,_hT,hcard⟩:=Finset.exists_subset_card_eq h
  exact ⟨T,hcard⟩

noncomputable def sixPoints : Finset F16 := Classical.choose exists_six_points

theorem sixPoints_card : sixPoints.card=6 := Classical.choose_spec exists_six_points

noncomputable def W : F16[X] := ∏a∈sixPoints,(X-C a)
noncomputable def P : F16[X] := W /ₘ (X^3)
noncomputable def R : F16[X] := -(W %ₘ (X^3))

theorem W_monic : W.Monic := monic_prod_X_sub_C id sixPoints

theorem W_degree : W.natDegree=6 := by
  unfold W
  rw [natDegree_prod_of_monic sixPoints (fun a=>X-C a) (fun a _=>monic_X_sub_C a)]
  simpa only [natDegree_X_sub_C,Finset.sum_const,smul_eq_mul,mul_one] using sixPoints_card

theorem P_degree : P.natDegree=3 := by
  unfold P
  rw [natDegree_divByMonic W (monic_X.pow 3),W_degree]
  simp

theorem R_degree : R.natDegree<3 := by
  unfold R
  rw [natDegree_neg]
  have h : (X^3 : F16[X])≠1 := by
    intro he
    have hh:=congrArg Polynomial.natDegree he
    norm_num at hh
  simpa only [natDegree_X_pow] using natDegree_modByMonic_lt W (monic_X.pow 3) h

theorem split_identity : X^3*P-R=W := by
  have h:=modByMonic_add_div W (X^3)
  unfold P R
  rw [sub_neg_eq_add]
  exact (add_comm _ _).trans h

theorem W_eval_zero_iff (x : F16) : W.eval x=0 ↔ x∈sixPoints := by
  simp only [W,eval_prod,eval_sub,eval_X,eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero]
  constructor
  · rintro ⟨a,ha,h⟩
    exact h.symm ▸ ha
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem agreement_iff (x : F16) : (X^3*P).eval x=R.eval x ↔ x∈sixPoints := by
  rw [←sub_eq_zero,←eval_sub,split_identity,W_eval_zero_iff]

theorem R_mem_actual_RS : (fun x=>R.eval x)∈RS evaluationSet (dKE 4 2) := by
  refine ⟨R,?_,fun _ _=>rfl⟩
  rw [printed_parameters]
  exact R_degree.le

theorem actual_distance :
    fracDist evaluationSet (fun x=>(X^3*P).eval x) (fun x=>R.eval x)=(10:ℝ)/16 := by
  classical
  have hf : evaluationSet.filter (fun x=>(X^3*P).eval x≠R.eval x)=
      evaluationSet\sixPoints := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_sdiff,ne_eq,agreement_iff]
  have hsub : sixPoints⊆evaluationSet := by intro x _;exact Finset.mem_univ x
  unfold fracDist
  rw [hf,Finset.card_sdiff_of_subset hsub,evaluationSet_card,sixPoints_card]
  norm_num

/-- Closed concrete witness, using the actual RS and fractional-distance definitions. -/
theorem printed_case2_distance_counterexample :
    evaluationSet.card=2^4 ∧ Module.finrank (ZMod 2) F16=4 ∧
    P.natDegree=3 ∧ 0<P.natDegree ∧ P.natDegree≤dKE 4 2 ∧
    (fun x=>R.eval x)∈RS evaluationSet (dKE 4 2) ∧
    fracDist evaluationSet (fun x=>(X^(dKE 4 2-0)*P).eval x) (fun x=>R.eval x)<(3:ℝ)/4 := by
  refine ⟨evaluationSet_card,field_binary_dimension,P_degree,?_,?_,R_mem_actual_RS,?_⟩
  · rw [P_degree];decide
  · rw [P_degree,printed_parameters]
  · rw [printed_parameters,Nat.sub_zero,actual_distance]
    norm_num

end NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance
