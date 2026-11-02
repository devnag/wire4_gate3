import Proof.Quartic.StageCert.TupleOrder

set_option autoImplicit false

namespace NearQuarticWires.StageCert

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual prefix order property for bounded occurrence
tuples, with positions outside the visited prefix ignored. -/
def PrefixIncreasing (value : ℕ→ℕ) (count : ℕ) : Prop :=
  ∀ i j, i<j→j<count→value i<value j

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the empty tuple has its original unit subset coefficient. -/
theorem prefixIncreasing_zero (value : ℕ→ℕ) : PrefixIncreasing value 0 := by
  intro i j hij hj
  omega

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: transitivity makes the literal adjacent-comparison loop
an exact test of the complete strict tuple-order coefficient. -/
theorem prefixIncreasing_succ (value : ℕ→ℕ) (count : ℕ) :
    PrefixIncreasing value (count+1) ↔
      PrefixIncreasing value count ∧ (count=0 ∨ value (count-1)<value count) := by
  constructor
  · intro h
    refine ⟨fun i j hij hj=>h i j hij (by omega),?_⟩
    by_cases hz : count=0
    · exact Or.inl hz
    · exact Or.inr (h (count-1) count (by omega) (by omega))
  · rintro ⟨h,hlast⟩ i j hij hj
    by_cases hj' : j<count
    · exact h i j hij hj'
    · have hjn : j=count := by omega
      subst j
      have hn : count≠0 := by omega
      have hlast' : value (count-1)<value count := hlast.resolve_left hn
      by_cases hi : i=count-1
      · simpa only [hi] using hlast'
      · exact (h i (count-1) (by omega) (by omega)).trans hlast'

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the completed finite prefix is precisely the strictly
increasing finite function used by the original subset polynomial. -/
theorem prefixIncreasing_fin (value : ℕ→ℕ) (count : ℕ) :
    PrefixIncreasing value count ↔ StrictMono (fun i : Fin count=>value i.val) := by
  constructor
  · intro h i j hij
    exact h i.val j.val hij j.isLt
  · intro h i j hij hj
    exact h (show (⟨i,by omega⟩ : Fin count)<⟨j,hj⟩ from hij)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the finite bounded-tuple order test is a computable Boolean
quantity, rather than an unbounded universal-quantifier oracle. -/
def prefixIncreasingBit (value : ℕ→ℕ) (count : ℕ) : Bool :=
  decide (StrictMono (fun i : Fin count=>value i.val))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the finite Boolean coefficient is exactly its original
strict-prefix meaning. -/
theorem prefixIncreasingBit_true (value : ℕ→ℕ) (count : ℕ) :
    prefixIncreasingBit value count=true ↔ PrefixIncreasing value count := by
  simp only [prefixIncreasingBit,decide_eq_true_eq,prefixIncreasing_fin]

end NearQuarticWires.StageCert
