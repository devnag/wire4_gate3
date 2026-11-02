import Proof.Quartic.StagePrint.BuilderMoments

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open scoped BigOperators
open NearCubicWires NearQuarticWires
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator

/-- `lem:print`(b,c), paper/paper.tex: zero terms outside the structural set allow a complete finite enumeration. -/
theorem sum_eq_structural {V : Type*} [Fintype V] (P : V → Prop) [DecidablePred P]
    (f : V → ℤ) (hz : ∀ x, ¬P x → f x = 0) :
    (∑ x, f x) = ∑ x : {x // P x}, f x.val := by
  have h := Fintype.sum_subtype_add_sum_subtype P f
  have hc : (∑ x : {x // ¬P x}, f x.val) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hz x.val x.property
  rw [hc, add_zero] at h
  exact h.symm

/-- `def:mask` and `lem:print`(b), paper/paper.tex: the literal integer mask polynomial vanishes on every structurally excluded walk, even for a failing witness. -/
theorem walkMaskPoly_zero_of_not_structural {N m : ℕ} (hm : 0 < m)
    (structural : Sampler.Cell N → Bool) (tau Xmax : ℕ) (X : Sampler.Cell N → ℕ)
    (walk : Cycle.Walk N m) (hn : ¬∀ e, structural (Cycle.edge hm walk e) = true) :
    Walks.walkMaskPoly hm structural tau Xmax X walk = 0 := by
  classical
  push Not at hn
  obtain ⟨e, he⟩ := hn
  unfold Walks.walkMaskPoly
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  cases hb : structural (Cycle.edge hm walk e) <;> simp_all [Mask.maskPolyEval]

/-- `eq:testE` and `lem:print`(b), paper/paper.tex: appending every walk's formula before a single table print yields the exact digit moment. -/
theorem callDigitMoment_sum (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (j : Fin 2) (sigma : Cycle.SignPattern 4)
    (r : Fin (p.J - 1 + 1)) :
    (∑ walk : Cycle.Walk hs.seedParameters.N 4,
      (callMomentFormula c hs w walk j (callDigitWeights c hs w j r) sigma).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
          (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z)))) =
      Walks.maskedMoment (4*p.k)
        (fun walk : Walks.StructuralWalk (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural =>
          Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
            (Builder.columnData c hs w z).X walk.val)
        (fun walk => (Builder.columnData c hs w z).E j sigma walk.val r) := by
  classical
  simp_rw [callDigitMoment_eval]
  unfold Walks.maskedMoment
  have he : 8*p.k = 2*(4*p.k) := by omega
  rw [he]
  apply sum_eq_structural
  intro walk hn
  rw [walkMaskPoly_zero_of_not_structural _ _ _ _ _ _ hn, zero_mul]

/-- `eq:testPhi` and `lem:print`(b), paper/paper.tex: appending every walk's formula before a single table print yields the exact complete final-error moment. -/
theorem callFinalMoment_sum (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (j : Fin 2) (sigma : Cycle.SignPattern 4) :
    (∑ walk : Cycle.Walk hs.seedParameters.N 4,
      (callMomentFormula c hs w walk j (callFinalWeights c p w j) sigma).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
          (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z)))) =
      Walks.maskedMoment (4*p.k)
        (fun walk : Walks.StructuralWalk (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural =>
          Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
            (Builder.columnData c hs w z).X walk.val)
        (fun walk => (Builder.columnData c hs w z).phi (by norm_num : 0 < 4) j sigma walk.val) := by
  classical
  simp_rw [callFinalMoment_eval]
  unfold Walks.maskedMoment
  have he : 8*p.k = 2*(4*p.k) := by omega
  rw [he]
  apply sum_eq_structural
  intro walk hn
  rw [walkMaskPoly_zero_of_not_structural _ _ _ _ _ _ hn, zero_mul]

end NearQuarticWires.StagePrint
