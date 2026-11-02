import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false

namespace NearQuarticWires.Mask

open scoped BigOperators

/-- Paper `def:mask`: coordinates whose actual occurrence incidence
degree is at least the integer cutoff. -/
def heavyCoordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ι → ℕ) (dstar : ℕ) : Finset ι :=
  Finset.univ.filter fun i => dstar ≤ degree i

/-- Paper `def:mask`: a pair is retained if at least one
of its actual flipped-coordinate sets avoids all heavy coordinates. -/
def structuralMask {ι α β : Type*} [DecidableEq ι]
    (left : α → Finset ι) (right : β → Finset ι) (heavy : Finset ι)
    (u : α) (v : β) : Bool :=
  decide (Disjoint (left u) heavy ∨ Disjoint (right v) heavy)

/-- Paper `lem:smaskpop`: an avoiding pattern only meets
coordinates with actual incidence degree strictly below `dstar`. -/
theorem degree_lt_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ι → ℕ) (dstar : ℕ) (s : Finset ι)
    (hs : Disjoint s (heavyCoordinates degree dstar)) :
    ∀ i ∈ s, degree i < dstar := by
  intro i hi
  by_contra h
  have hmem : i ∈ heavyCoordinates degree dstar := by
    simp [heavyCoordinates, Nat.le_of_not_gt h]
  exact Finset.disjoint_left.mp hs hi hmem

/-- Paper `lem:smaskpop`: the exact incidence sum of an
avoiding pattern is strictly below the half-block-count times `dstar`. -/
theorem incidence_sum_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ι → ℕ) (dstar halfBlocks : ℕ) (s : Finset ι)
    (hd : 0 < dstar) (hr : 0 < halfBlocks) (hcard : s.card ≤ halfBlocks)
    (hs : Disjoint s (heavyCoordinates degree dstar)) :
    ∑ i ∈ s, degree i < halfBlocks * dstar := by
  have hdeg := degree_lt_of_disjoint degree dstar s hs
  have hsum : ∑ i ∈ s, degree i ≤ s.card * (dstar - 1) := by
    calc
      _ ≤ ∑ _i ∈ s, (dstar - 1) := Finset.sum_le_sum fun i hi => by
        have := hdeg i hi
        omega
      _ = _ := by simp
  have hmul : s.card * (dstar - 1) ≤ halfBlocks * (dstar - 1) :=
    Nat.mul_le_mul_right _ hcard
  have hstrict : halfBlocks * (dstar - 1) < halfBlocks * dstar := by
    apply Nat.mul_lt_mul_of_pos_left _ hr
    omega
  exact hsum.trans_lt (hmul.trans_lt hstrict)

/-- Paper `lem:smaskpop`: the structural mask gives the
population cap from the two actual mixed-dependence incidence bounds. -/
theorem structural_population_lt {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ι → ℕ) (left : α → Finset ι) (right : β → Finset ι)
    (dstar halfBlocks : ℕ) (population : α → β → ℕ)
    (hd : 0 < dstar) (hr : 0 < halfBlocks)
    (hleft : ∀ u, (left u).card ≤ halfBlocks)
    (hright : ∀ v, (right v).card ≤ halfBlocks)
    (hpop_left : ∀ u v, population u v ≤ ∑ i ∈ left u, degree i)
    (hpop_right : ∀ u v, population u v ≤ ∑ i ∈ right v, degree i)
    (u : α) (v : β)
    (hmask : structuralMask left right (heavyCoordinates degree dstar) u v = true) :
    population u v < halfBlocks * dstar := by
  have h : Disjoint (left u) (heavyCoordinates degree dstar) ∨
      Disjoint (right v) (heavyCoordinates degree dstar) := by
    simpa only [structuralMask, decide_eq_true_eq] using hmask
  rcases h with h | h
  · exact (hpop_left u v).trans_lt
      (incidence_sum_lt degree dstar halfBlocks (left u) hd hr (hleft u) h)
  · exact (hpop_right u v).trans_lt
      (incidence_sum_lt degree dstar halfBlocks (right v) hd hr (hright v) h)

/-- Paper `lem:smaskmass`: the number of heavy coordinates
is paid by the actual total bottom incidence, hence by the wire budget. -/
theorem heavy_card_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ι → ℕ) (dstar W : ℕ) (hW : ∑ i, degree i ≤ W) :
    (heavyCoordinates degree dstar).card * dstar ≤ W := by
  calc
    _ = ∑ _i ∈ heavyCoordinates degree dstar, dstar := by simp
    _ ≤ ∑ i ∈ heavyCoordinates degree dstar, degree i :=
      Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, degree i := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ W := hW

end NearQuarticWires.Mask
