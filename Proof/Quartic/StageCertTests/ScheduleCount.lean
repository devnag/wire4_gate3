import Proof.Quartic.StageCertTests.WholeSchedule

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

/-- `sec:cycle`, paper/paper.tex:
exactly half of the 256 binary sign patterns have nonzero κ. -/
def activeSignCodes : List (Fin 256) :=
  (List.finRange 256).filter fun code => decide (Cycle.kappa 4 (patternOfCode code.val) ≠ 0)

/-- `sec:cycle`, paper/paper.tex:
the exact nonzero-κ count is checked by finite binary parity. -/
theorem activeSignCodes_length : activeSignCodes.length = 128 := by
  unfold activeSignCodes
  have he : (fun code : Fin 256 => decide (Cycle.kappa 4 (patternOfCode code.val) ≠ 0)) =
      (fun code : Fin 256 => decide (lowerBitSum 8 code.val%2=0)) := by
    funext code
    exact kappa_patternOfCode code
  rw [he]
  decide +kernel

/-- `eq:testE`–`eq:testPhi`, paper/paper.tex:
one active pattern contributes precisely one test per selected
digit and one final-error test. -/
theorem patternMetadataList_length (p : Cells.Parameters) (j : Fin 2) (code : Fin 256) :
    (patternMetadataList p j code).length = p.J+1 := by
  simp [patternMetadataList,digitMetadataList]

/-- `sec:algorithm`, paper/paper.tex:
filtering the binary sign enumeration counts whole-test blocks,
independently of any column or walk population. -/
theorem activePatternMetadata_length (codes : List (Fin 256)) (p : Cells.Parameters) (j : Fin 2) :
    (codes.flatMap (activePatternMetadata p j)).length =
      (codes.filter (fun code => decide (Cycle.kappa 4 (patternOfCode code.val) ≠ 0))).length*(p.J+1) := by
  induction codes with
  | nil => simp
  | cons code codes ih =>
      by_cases hk : Cycle.kappa 4 (patternOfCode code.val) ≠ 0
      · simp [activePatternMetadata,hk,ih,patternMetadataList_length,Nat.add_mul,Nat.add_comm]
      · simp [activePatternMetadata,hk,ih]

/-- `sec:algorithm`, paper/paper.tex:
the exact active whole-test count for each circuit is 128 times
the chain length plus its final-error test. -/
theorem circuitMetadataList_length (p : Cells.Parameters) (j : Fin 2) :
    (circuitMetadataList p j).length = 128*(p.J+1) := by
  simp only [circuitMetadataList,circuitMetadataBlocks,List.ofFn_eq_map,List.flatten_eq_flatMap,
    List.flatMap_map,id_eq]
  rw [activePatternMetadata_length]
  change activeSignCodes.length*(p.J+1) = _
  rw [activeSignCodes_length]

/-- `sec:algorithm`, paper/paper.tex:
the physical outer circuit loop counts complete sign-filtered
test blocks with no padded or spurious active circuit. -/
theorem circuitMetadataForLimit_length (p : Cells.Parameters) (count : ℕ) (hc : count ≤ 2) :
    (circuitMetadataForLimit p count hc).length = count*(128*(p.J+1)) := by
  simp [circuitMetadataForLimit,List.length_flatten,List.map_ofFn,Function.comp_def,
    circuitMetadataList_length,List.ofFn_const]

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the full actual scheduler emits exactly
this many five-field whole-test requests, so the outer controller
can construct its loop bound from selected public scalars. -/
theorem certificateMetadata_length (p : Cells.Parameters) (kind : NearCubicGates.Close.Interfaces.CallKind) :
    (certificateMetadata p kind).length = 1+(callCircuitCount kind)*(128*(p.J+1)) := by
  simp only [certificateMetadata,List.length_cons,circuitMetadataForLimit_length]
  omega

end NearQuarticWires.StageCertTests
