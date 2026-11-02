import Proof.Quartic.Reconstruct.PointsProgram

/-!
# The written points are the points of the box

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`boxPointsWord_eq`: when the two coordinate lists of a box are the intervals `lo'_j - B_j, lo'_j - B_j + 1, …` with
`len_j` points (`BoxArith.boxAxisOf_eq`), the word of its points `listWord (listWord intWord) (boxPoints …)` is the
word written by `pointsS` (`PointsProgram.pointsS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

/-- **The points of a box as written.** -/
theorem boxPointsWord_eq (lo0 len0 B0 lo1 len1 B1 : ℕ) (ax0 ax1 : List ℤ)
    (h0 : ax0 = (List.range len0).map fun i : ℕ => ((lo0 : ℕ) : ℤ) - B0 + (i : ℤ))
    (h1 : ax1 = (List.range len1).map fun i : ℕ => ((lo1 : ℕ) : ℤ) - B1 + (i : ℤ)) :
    listWord (listWord NearCubicGates.Close.Interfaces.intWord) ((ax0 ×ˢ ax1).map pairList) =
      natWord (len0 * len1) ++ pointsWord lo0 len0 B0 lo1 len1 B1 := by
  subst h0 h1
  unfold listWord
  congr 1
  · simp [List.length_product]
  · simp only [SProd.sprod, List.product, List.flatMap_map, List.map_flatMap, List.flatMap_assoc,
      pointsWord]
    refine List.flatMap_congr fun i _ => ?_
    unfold rowPointsWord
    refine List.flatMap_congr fun j _ => ?_
    simp only [pairList, pointWord, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_cons, List.length_nil, List.append_assoc]
    push_cast
    ring_nf

end NearQuarticWires.Reconstruct
