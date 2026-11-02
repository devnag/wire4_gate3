import Proof.Quartic.StageCertTests.TestMetadata

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

attribute [local instance] Classical.propDecidable

/-- `sec:algorithm`, paper/paper.tex:
the physical sign ordinals enumerate the same required whole-test
tables as the literal mathematical certificate. -/
noncomputable def ordinalTestPlan (J : ℕ) (circuits : Finset (Fin 2)) : List (TestOrdinal J) :=
  .population :: (List.finRange 2).flatMap fun j =>
    if j ∈ circuits then (List.finRange 256).flatMap (fun code =>
      if Cycle.kappa 4 (patternOfCode code.val) ≠ 0 then
        (List.ofFn fun r : Fin (J+1) => TestOrdinal.digit j code r) ++ [.finalError j code]
      else []) else []

/-- `sec:algorithm`, paper/paper.tex:
binary ordinal scheduling preserves every required test and its
exact order, including the population and final-error tests. -/
theorem ordinalTestPlan_kind (J : ℕ) (circuits : Finset (Fin 2)) :
    (ordinalTestPlan J circuits).map TestOrdinal.kind = testPlan J circuits := by
  simp only [ordinalTestPlan,testPlan,List.map_cons,TestOrdinal.kind,List.map_flatMap]
  congr 1
  apply congrArg (fun f : Fin 2 → List (TestKind J) => (List.finRange 2).flatMap f)
  funext j
  by_cases hj : j ∈ circuits
  · simp only [hj,if_pos,List.map_flatMap]
    rw [StageCert.signPatterns,List.ofFn_eq_map,List.flatMap_map]
    apply congrArg (fun f : Fin 256 → List (TestKind J) => (List.finRange 256).flatMap f)
    funext code
    change (if Cycle.kappa 4 (fun l : Fin 8 => code.val.testBit l.val) ≠ 0 then
      (List.ofFn fun r : Fin (J+1) => TestOrdinal.digit j code r) ++ [.finalError j code] else []).map
      TestOrdinal.kind =
        (if Cycle.kappa 4 (fun l : Fin 8 => code.val.testBit l.val) ≠ 0 then
          (List.ofFn fun r : Fin (J+1) => TestKind.digit j (fun l => code.val.testBit l.val) r) ++
            [.finalError j (fun l => code.val.testBit l.val)] else [])
    split_ifs
    · simp only [List.map_append,List.map_ofFn,List.map_cons,List.map_nil,TestOrdinal.kind]
      rfl
    · rfl
  · simp only [hj,if_false,List.map_nil]

end NearQuarticWires.StageCertTests
