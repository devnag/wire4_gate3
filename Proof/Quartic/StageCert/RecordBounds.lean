import Proof.Quartic.StageCert.ActualMoments

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open Finset
open NearQuarticWires
open NearCubicGates.Close.Interfaces (Call)

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p)

/-- `eq:testX`, paper/paper.tex: the unconditional population
moment is bounded before any column certificate is assumed. -/
theorem actual_population_abs_le (bits : List Bool) (z : Fin (2^(c.n-p.k))) :
    |(populationRecord p.k (Builder.columnData c hs bits z)).1| ≤
      ((p.N^2*(Builder.occurrences c 0+Builder.occurrences c 1)^(2*p.k) : ℕ) : ℤ) := by
  let D := Builder.columnData c hs bits z
  have hv (q : Walks.StructuralPoint D.structural) :
      |(D.X q.val : ℤ)| ≤ (Builder.occurrences c 0+Builder.occurrences c 1 : ℕ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast column_X_le c hs bits z q.val
  have h := maskedMoment_abs_le p.k 1
    (Builder.occurrences c 0+Builder.occurrences c 1)
    (fun _ : Walks.StructuralPoint D.structural => (1:ℤ))
    (fun q => (D.X q.val : ℤ)) (by intro q; norm_num) hv
  have hc : Fintype.card (Walks.StructuralPoint D.structural) ≤ p.N^2 := by
    calc
      _ ≤ Fintype.card (Sampler.Cell hs.seedParameters.N) := Fintype.card_subtype_le _
      _ = hs.seedParameters.N^2 := by simp [Sampler.Cell]; ring
      _ = p.N^2 := by rw [Cells.ParameterRules.seed_N hs]
  change |Walks.momentSum p.k (fun q : Walks.StructuralPoint D.structural => (D.X q.val : ℤ))| ≤ _
  have h' : |Walks.momentSum p.k (fun q : Walks.StructuralPoint D.structural => (D.X q.val : ℤ))| ≤
      (Fintype.card (Walks.StructuralPoint D.structural) : ℤ)*
        (Builder.occurrences c 0+Builder.occurrences c 1 : ℕ)^(2*p.k) := by
    simpa only [Walks.maskedMoment,Walks.momentSum,Nat.cast_one,one_mul,mul_one] using h
  refine h'.trans ?_
  push_cast
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: all signed
record magnitudes and literal strict thresholds fit one polynomial-height
power of two, for every arbitrary witness word and original column. -/
theorem columnRecords_selected_bound (B1 : ℕ) (hb : 1 ≤ c.radius*(c.n:ℚ)^B1)
    (bits : List Bool) (z : Fin (2^(c.n-p.k))) :
    ∀ r ∈ columnRecords p.k (Builder.columnData c hs bits z),
      |r.1| ≤ (2:ℤ)^(Cells.ParameterArithmetic.certificateBitEnvelope
        (Cells.ParameterArithmetic.preparationEnvelope B1 c.n)) ∧
      r.2 ≤ 2^(Cells.ParameterArithmetic.certificateBitEnvelope
        (Cells.ParameterArithmetic.preparationEnvelope B1 c.n)) := by
  classical
  let D := Builder.columnData c hs bits z
  let bound := Cells.ParameterArithmetic.certificateBitEnvelope
    (Cells.ParameterArithmetic.preparationEnvelope B1 c.n)
  obtain ⟨hpop,hX,hE,hPhi⟩ := hs.selected_other_moment_power_bounds B1 hb
  have hp : |(populationRecord p.k D).1| ≤ (2:ℤ)^bound := by
    refine (actual_population_abs_le c hs bits z).trans ?_
    exact_mod_cast hpop
  have he (j : Fin 2) (σ : Cycle.SignPattern 4) (i : Fin (p.J-1+1)) :
      |(digitRecord p.k D j σ i).1| ≤ (2:ℤ)^bound := by
    exact actual_walk_moment_selected_bound c hs B1 hb bits z
      (fun w => D.E j σ w.val i) (fun w => digit_le_scoreRange c hs bits z j σ w.val i)
  have hf (j : Fin 2) (σ : Cycle.SignPattern 4) :
      |(finalRecord p.k D j σ).1| ≤ (2:ℤ)^bound := by
    exact actual_walk_moment_selected_bound c hs B1 hb bits z
      (fun w => D.phi (by norm_num) j σ w.val) (fun w => phi_le_scoreRange c hs bits z j σ w.val)
  intro r hr
  change r ∈ columnRecords p.k D at hr
  simp only [columnRecords,List.mem_cons,List.mem_flatMap,List.mem_finRange,true_and] at hr
  rcases hr with rfl | ⟨j,hj⟩
  · exact ⟨hp,hX⟩
  · by_cases hcir : j ∈ D.circuits
    · rw [if_pos hcir] at hj
      obtain ⟨σ,_hσ,hr⟩ := List.mem_flatMap.mp hj
      by_cases hk : Cycle.kappa 4 σ ≠ 0
      · rw [if_pos hk] at hr
        rcases List.mem_append.mp hr with hd | hf'
        · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
          refine ⟨he j σ i,?_⟩
          change p.hE^(2*(4*p.k)) ≤ _
          simpa only [show 2*(4*p.k)=8*p.k by omega,Builder.callInput] using hE
        · have : r=finalRecord p.k D j σ := by simpa using hf'
          subst r
          refine ⟨hf j σ,?_⟩
          change p.Lambda^(2*(4*p.k)) ≤ _
          simpa only [show 2*(4*p.k)=8*p.k by omega,Builder.callInput] using hPhi
      · simp [hk] at hr
    · simp [hcir] at hj

end NearQuarticWires.StageCert
