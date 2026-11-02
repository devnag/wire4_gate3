import SourceAdapters.Vacuity.BCGT13Case2Distance

/-!
# The same printed distance assertion at positive degree

BCGT13, ECCC TR12-045 revision 3, Lemma 11.10 Case 2, p.67:
at `κ=4`, `η=2`, `d=1`, a monic polynomial with five distinct roots
gives fractional distance `11/16`, below the printed `3/4` threshold.
The field, binary subspace, RS code and distance are the same concrete
ones as in the degree-zero witness.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive

open Polynomial
open NearCubicGates.Published.BCGT13
open NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance

private theorem exists_five_points : ∃T : Finset F16,T.card=5 := by
  have h : 5 ≤ (Finset.univ : Finset F16).card := by
    rw [Finset.card_univ,field_card]
    decide
  obtain ⟨T,_hT,hcard⟩:=Finset.exists_subset_card_eq h
  exact ⟨T,hcard⟩

noncomputable def fivePoints : Finset F16 := Classical.choose exists_five_points

theorem fivePoints_card : fivePoints.card=5 := Classical.choose_spec exists_five_points

noncomputable def W5 : F16[X] := ∏a∈fivePoints,(X-C a)
noncomputable def P1 : F16[X] := W5 /ₘ (X^2)
noncomputable def R1 : F16[X] := -(W5 %ₘ (X^2))

theorem W5_monic : W5.Monic := monic_prod_X_sub_C id fivePoints

theorem W5_degree : W5.natDegree=5 := by
  unfold W5
  rw [natDegree_prod_of_monic fivePoints (fun a=>X-C a) (fun a _=>monic_X_sub_C a)]
  simpa only [natDegree_X_sub_C,Finset.sum_const,smul_eq_mul,mul_one] using fivePoints_card

theorem P1_degree : P1.natDegree=3 := by
  unfold P1
  rw [natDegree_divByMonic W5 (monic_X.pow 2),W5_degree]
  simp

theorem R1_degree : R1.natDegree<2 := by
  unfold R1
  rw [natDegree_neg]
  have h : (X^2 : F16[X])≠1 := by
    intro he
    have hh:=congrArg Polynomial.natDegree he
    norm_num at hh
  simpa only [natDegree_X_pow] using natDegree_modByMonic_lt W5 (monic_X.pow 2) h

theorem split_identity : X^2*P1-R1=W5 := by
  have h:=modByMonic_add_div W5 (X^2)
  unfold P1 R1
  rw [sub_neg_eq_add]
  exact (add_comm _ _).trans h

theorem W5_eval_zero_iff (x : F16) : W5.eval x=0 ↔ x∈fivePoints := by
  simp only [W5,eval_prod,eval_sub,eval_X,eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp only [sub_eq_zero]
  constructor
  · rintro ⟨a,ha,h⟩
    exact h.symm ▸ ha
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem agreement_iff (x : F16) : (X^2*P1).eval x=R1.eval x ↔ x∈fivePoints := by
  rw [←sub_eq_zero,←eval_sub,split_identity,W5_eval_zero_iff]

theorem R1_mem_actual_RS : (fun x=>R1.eval x)∈RS evaluationSet (dKE 4 2) := by
  refine ⟨R1,?_,fun _ _=>rfl⟩
  rw [printed_parameters]
  exact R1_degree.le.trans (by decide)

theorem actual_distance_positive :
    fracDist evaluationSet (fun x=>(X^2*P1).eval x) (fun x=>R1.eval x)=(11:ℝ)/16 := by
  classical
  have hf : evaluationSet.filter (fun x=>(X^2*P1).eval x≠R1.eval x)=
      evaluationSet\fivePoints := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_sdiff,ne_eq,agreement_iff]
  have hsub : fivePoints⊆evaluationSet := by intro x _;exact Finset.mem_univ x
  unfold fracDist
  rw [hf,Finset.card_sdiff_of_subset hsub,evaluationSet_card,fivePoints_card]
  norm_num

/-- A closed counterexample with `d=1`, using the actual code and distance. -/
theorem positive_degree_distance_counterexample :
    evaluationSet.card=2^4 ∧ Module.finrank (ZMod 2) F16=4 ∧
    P1.natDegree=3 ∧ 1<P1.natDegree ∧ P1.natDegree≤dKE 4 2 ∧
    (fun x=>R1.eval x)∈RS evaluationSet (dKE 4 2) ∧
    fracDist evaluationSet (fun x=>(X^(dKE 4 2-1)*P1).eval x) (fun x=>R1.eval x)<(3:ℝ)/4 := by
  refine ⟨evaluationSet_card,field_binary_dimension,P1_degree,?_,?_,R1_mem_actual_RS,?_⟩
  · rw [P1_degree];decide
  · rw [P1_degree,printed_parameters]
  · rw [printed_parameters]
    change fracDist evaluationSet (fun x=>(X^2*P1).eval x) (fun x=>R1.eval x)<(3:ℝ)/4
    rw [actual_distance_positive]
    norm_num

end NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive
