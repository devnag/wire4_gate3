import Proof.Quartic.Machine.Counts

set_option autoImplicit false

namespace NearQuarticWires.Machine

/-- `cor:conditional`, paper/paper.tex: unpadded radix `Q+1`.
Digit zero chooses the constant, and a successor chooses that sample. -/
def gammaChoiceEquiv (m Q : ℕ) : GammaChoice m Q ≃ Fin ((Q + 1) ^ (2 * m)) :=
  finFunctionFinEquiv

/-- `prop:time`, paper/paper.tex: exact occurrence-preserving
enumeration; no padding of the sample labels to the entire field. -/
def gammaChoices (m Q : ℕ) : List (GammaChoice m Q) :=
  List.ofFn (gammaChoiceEquiv m Q).symm

/-- `prop:time`, paper/paper.tex: the concrete enumeration has
exactly `(Q+1)^(2m)` iterations, not `2^(2m*ell_f)` iterations. -/
theorem gammaChoices_length (m Q : ℕ) :
    (gammaChoices m Q).length = (Q + 1) ^ (2 * m) := by
  simp [gammaChoices]

/-- `cor:conditional`, paper/paper.tex: every constant/sample
choice is retained by the exact mixed-radix enumeration. -/
theorem gammaChoices_complete (m Q : ℕ) (choice : GammaChoice m Q) :
    choice ∈ gammaChoices m Q := by
  apply List.mem_ofFn.mpr
  exact ⟨gammaChoiceEquiv m Q choice, (gammaChoiceEquiv m Q).symm_apply_apply choice⟩

/-- `cor:conditional`, paper/paper.tex: each expansion choice
is visited once, even when its underlying sample constraints repeat. -/
theorem gammaChoices_nodup (m Q : ℕ) : (gammaChoices m Q).Nodup := by
  apply List.nodup_ofFn.mpr
  exact (gammaChoiceEquiv m Q).symm.injective

/-- `sec:cycle`, paper/paper.tex: walk-major mixed-radix index. -/
def closedWalkEquiv (m N : ℕ) : ClosedWalk m N ≃ Fin (N ^ m * N ^ m) :=
  (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv).trans finProdFinEquiv

/-- `sec:algorithm`, paper/paper.tex: enumerate all closed walks
before applying the structural-mask filter. -/
def closedWalks (m N : ℕ) : List (ClosedWalk m N) :=
  List.ofFn (closedWalkEquiv m N).symm

/-- `prop:time`, paper/paper.tex: with `k=2kh` the concrete walk
list has exactly `2^(m*k)` entries, including repeated-vertex walks. -/
theorem closedWalks_length_two_pow (m kh : ℕ) :
    (closedWalks m (2 ^ kh)).length = 2 ^ (m * (2 * kh)) := by
  simp only [closedWalks, List.length_ofFn]
  rw [← pow_add, ← pow_mul]
  congr 1
  ring

end NearQuarticWires.Machine
