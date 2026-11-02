import Proof.Quartic.StageCert.SourceWeightDock

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Interfaces

/-- `eq:testE` and `lem:print`, paper/paper.tex: the physical signed digit weights extended by zeros to
the unchanged concatenated original occurrence bank. -/
def sourceDigitGlobalWeights (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (row : ℕ) (g : Fin (Builder.allGates c).length) : ℤ :=
  (selectedSummand j.val c.first.gates.length g.val
    (sourceDigitPositive bits (Builder.allGates c).length row p.J p.k g.val):ℤ)-
    selectedSummand j.val c.first.gates.length g.val
      (sourceDigitNegative bits p.factors (Builder.allGates c).length row p.J p.k g.val)

/-- `eq:testE` and `lem:print`, paper/paper.tex: physical bank filtering and retained coefficient arithmetic
give the exact original digit weight at every occurrence, including
all zeros outside the selected circuit and every repeated gate label. -/
theorem source_digit_global_eq_builder (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (j : Fin 2) (r : Fin (p.J-1+1)) (g : Fin (Builder.allGates c).length) :
    sourceDigitGlobalWeights c p bits j r.val g=
      StagePrint.circuitWeights c j (StagePrint.callDigitWeights c hs bits j r) g := by
  have hj : j=0 ∨ j=1 := by have hh := j.isLt; omega
  rcases hj with rfl | rfl
  · by_cases hg : g.val<c.first.gates.length
    · let t : Fin (Builder.occurrences c 0) := ⟨g.val,hg⟩
      have h := source_digit_weight_eq_builder c hs bits 0 r t
      simpa [sourceDigitGlobalWeights,selectedSummand,StagePrint.circuitWeights,
        hg,callOccurrenceOffset,t] using h
    · simp [sourceDigitGlobalWeights,selectedSummand,StagePrint.circuitWeights,hg]
  · by_cases hg : c.first.gates.length≤g.val
    · have hlen : g.val<c.first.gates.length+c.second.gates.length := by
        simpa only [Builder.allGates,List.length_append] using g.isLt
      let t : Fin (Builder.occurrences c 1) := ⟨g.val-c.first.gates.length,by
        change g.val-c.first.gates.length<c.second.gates.length
        omega⟩
      have h := source_digit_weight_eq_builder c hs bits 1 r t
      have hoff : callOccurrenceOffset c 1 t=g.val := by
        simp only [callOccurrenceOffset,Fin.reduceEq,ite_false]
        change c.first.gates.length+(g.val-c.first.gates.length)=g.val
        omega
      rw [hoff] at h
      simpa [sourceDigitGlobalWeights,selectedSummand,StagePrint.circuitWeights,hg,t] using h
    · simp [sourceDigitGlobalWeights,selectedSummand,StagePrint.circuitWeights,hg]

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the complete final-error weights on the unchanged
concatenated original occurrence bank. -/
def sourceFinalGlobalWeights (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (g : Fin (Builder.allGates c).length) : ℤ :=
  (selectedSummand j.val c.first.gates.length g.val
    (sourceFinalPositive bits (Builder.allGates c).length p.J p.k g.val p.M1):ℤ)-
    selectedSummand j.val c.first.gates.length g.val p.A

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the physical final-error coefficient is exactly its
Builder zero extension, including signed cancellation and unselected banks. -/
theorem source_final_global_eq_builder (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (g : Fin (Builder.allGates c).length) :
    sourceFinalGlobalWeights c p bits j g=
      StagePrint.circuitWeights c j (StagePrint.callFinalWeights c p bits j) g := by
  have hj : j=0 ∨ j=1 := by have hh := j.isLt; omega
  rcases hj with rfl | rfl
  · by_cases hg : g.val<c.first.gates.length
    · let t : Fin (Builder.occurrences c 0) := ⟨g.val,hg⟩
      have h := source_final_weight_eq_builder c p bits 0 t
      simpa [sourceFinalGlobalWeights,selectedSummand,StagePrint.circuitWeights,
        hg,callOccurrenceOffset,t] using h
    · simp [sourceFinalGlobalWeights,selectedSummand,StagePrint.circuitWeights,hg]
  · by_cases hg : c.first.gates.length≤g.val
    · have hlen : g.val<c.first.gates.length+c.second.gates.length := by
        simpa only [Builder.allGates,List.length_append] using g.isLt
      let t : Fin (Builder.occurrences c 1) := ⟨g.val-c.first.gates.length,by
        change g.val-c.first.gates.length<c.second.gates.length
        omega⟩
      have h := source_final_weight_eq_builder c p bits 1 t
      have hoff : callOccurrenceOffset c 1 t=g.val := by
        simp only [callOccurrenceOffset,Fin.reduceEq,ite_false]
        change c.first.gates.length+(g.val-c.first.gates.length)=g.val
        omega
      rw [hoff] at h
      simpa [sourceFinalGlobalWeights,selectedSummand,StagePrint.circuitWeights,hg,t] using h
    · simp [sourceFinalGlobalWeights,selectedSummand,StagePrint.circuitWeights,hg]

end NearQuarticWires.StageCert.Tokens
