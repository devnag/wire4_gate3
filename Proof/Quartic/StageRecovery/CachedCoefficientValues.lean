import Proof.Quartic.StageRecovery.BoundedCoefficients
import Proof.Gates.Expand.PrintVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the original bounded
family's support order equals its canonical finite-set order. -/
theorem famPairs_supports (V D : ℕ) :
    (famPairs V D).map (fun p => setOf V p.1) = famS V D := by
  rw [famS, fam_eq_pairs, List.map_map]
  rfl

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the actual bounded scan value is exactly the canonical nonnegative
coefficient residue, rather than only a congruent signed integer. -/
theorem boundedFormulaCache_value {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V)
    (D : ℕ) (p : ℕ × ℕ) (hp : p ∈ famPairs V D) :
    ((boundedFormulaCache q F D).foldl (cachedMobStep q V p.1 (p.2 % 2)) 0 : ℕ) =
      (coeff F.expand (setOf V p.1) % (q : ℤ)).toNat := by
  have hd := famPairs_le V D p hp
  have hcard := (famPairs_mem V D p hp).2
  have h := boundedFormulaCache_coefficient q hq F D p.1 (hcard.le.trans hd)
  rw [hcard] at h
  have hb := cachedMobFold_lt q V p.1 (p.2 % 2) 0
    (boundedFormulaCache q F D) hq hq
  have hbz : (((boundedFormulaCache q F D).foldl (cachedMobStep q V p.1 (p.2 % 2)) 0 : ℕ) : ℤ) < q := by
    exact_mod_cast hb
  unfold Int.ModEq at h
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hbz] at h
  exact congrArg Int.toNat h

/-- `lem:print`, paper/paper.tex: the physical
coefficient store is the exact canonical bounded-term coefficient list. -/
theorem cachedCoefficients_eq_bounded {V : ℕ} (q : ℕ) (hq : 0 < q)
    (F : Formula V) (D : ℕ) :
    cachedCoefficients q V (boundedFormulaCache q F D) =
      (boundedModTerms q F D).map (fun t => t.2.toNat) := by
  unfold cachedCoefficients boundedFormulaCache pointEntries
  rw [List.map_map]
  unfold boundedModTerms
  rw [List.map_map, ← famPairs_supports, List.map_map]
  apply List.map_congr_left
  intro p hp
  exact boundedFormulaCache_value q hq F D p hp

/-- `lem:print`, paper/paper.tex: the retained outer
support store is exactly aligned with the canonical Terms stream. -/
theorem boundedFormulaCache_supports {V : ℕ} (q : ℕ) (F : Formula V) (D : ℕ) :
    (boundedFormulaCache q F D).map Prod.fst = fam V D := by
  rw [boundedFormulaCache, pointEntries, List.map_map, fam_eq_pairs]
  rfl

end NearQuarticWires.StageRecovery
