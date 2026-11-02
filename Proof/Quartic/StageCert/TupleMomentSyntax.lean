import Proof.Quartic.StageCert.TupleSourceBounds
import Proof.Quartic.StageCert.TupleMoments

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator
open Cells.ParameterArithmetic

/-- `lem:print`, paper/paper.tex: eight actual
tuple masks contribute additively to the emitted moment's syntax,
while the literal even exponent contributes its full unary length. -/
theorem tupleCallMomentFormula_size_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4) :
    (tupleCallMomentFormula c hs w walk j f sigma).size ≤
      8*((p.Xmax+1)*(((Builder.allGates c).length+1)^p.Xmax*(11*p.Xmax+4)+4)+4)+
        82*(Builder.allGates c).length+8*p.k+4 := by
  have hm := StageLift.prodList_size_le
    (List.ofFn fun edge : Fin 8=>tupleMaskFormula (StagePrint.callStructural c hs walk edge)
      (StagePrint.selectedSquare (by decide : 0<4) (Builder.selection c (p:=p) w) edge)
      p.tau p.Xmax)
    ((p.Xmax+1)*(((Builder.allGates c).length+1)^p.Xmax*(11*p.Xmax+4)+4)+3) (by
      intro F hF
      obtain ⟨edge,rfl⟩ := List.mem_ofFn.mp hF
      exact StageLift.selectedTupleMask_size_le _ _ _ _ _ _)
  simp only [List.length_ofFn] at hm
  have hf := StageLift.walkFormula_size_le (StagePrint.circuitWeights c j f)
    (fun e=>Cycle.signValue (sigma e))
    (fun g e corner=>Cells.atomIndex (Cells.cornerRole (by decide : 0<4) e corner) g)
  change (StagePrint.callWalkFormula c j f sigma).size≤(Builder.allGates c).length*82+1 at hf
  change (Cells.walkMaskFormula _).size+((StagePrint.callWalkFormula c j f sigma).size+8*p.k+1)+1≤_
  change (Cells.walkMaskFormula (fun edge=>tupleMaskFormula
    (StagePrint.callStructural c hs walk edge)
    (StagePrint.selectedSquare (by decide : 0<4) (Builder.selection c (p:=p) w) edge)
    p.tau p.Xmax)).size≤_ at hm
  omega

/-- `lem:print`, paper/paper.tex: the actual
integer-weight construction bound retains the tuple factor, the
linear source leaf bits and the complete moment exponent. -/
theorem tupleCallMomentFormula_weight_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4) (L : ℕ)
    (hw : ∀g,Nat.size (StagePrint.circuitWeights c j f g).natAbs≤L) :
    (tupleCallMomentFormula c hs w walk j f sigma).weight ≤
      8*(1+(p.Xmax+1)*(p.Xmax+2+((Builder.allGates c).length+1)^p.Xmax*(8*p.Xmax+3)))+1+
        8*p.k*((Builder.allGates c).length*(8*(L+5)+1)) := by
  have hm := cert_prodList_weight_le
    (List.ofFn fun edge : Fin 8=>tupleMaskFormula (StagePrint.callStructural c hs walk edge)
      (StagePrint.selectedSquare (by decide : 0<4) (Builder.selection c (p:=p) w) edge)
      p.tau p.Xmax)
    (1+(p.Xmax+1)*(p.Xmax+2+((Builder.allGates c).length+1)^p.Xmax*(8*p.Xmax+3))) (by
      intro F hF
      obtain ⟨edge,rfl⟩ := List.mem_ofFn.mp hF
      simpa only [Nat.mul_comm p.Xmax 8] using
        tupleMaskFormula_weight_le (StagePrint.callStructural c hs walk edge)
          (StagePrint.selectedSquare (by decide : 0<4) (Builder.selection c (p:=p) w) edge)
          p.tau p.Xmax 8
          (cert_selected_square_weight_le (by decide : 0<4) (Builder.selection c (p:=p) w) edge))
  simp only [List.length_ofFn] at hm
  have hf := cert_pooled_walk_weight_le (by decide : 0<4) (StagePrint.circuitWeights c j f)
    (fun e=>Cycle.signValue (sigma e)) L hw (fun e=>by cases sigma e <;> decide)
  change (StagePrint.callWalkFormula c j f sigma).weight≤_ at hf
  change (Cells.walkMaskFormula _).weight+8*p.k*(StagePrint.callWalkFormula c j f sigma).weight≤_
  exact Nat.add_le_add hm (Nat.mul_le_mul_left _ hf)

/-- `lem:print`, paper/paper.tex: every literal
constant of the actual tuple moment is bounded by the larger of
its Newton order and original complete-score coefficient bits. -/
theorem tupleCallMomentFormula_constant_bits (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4) (L : ℕ)
    (hX : p.Xmax+1≤L)
    (hw : ∀g,Nat.size (StagePrint.circuitWeights c j f g).natAbs≤L) :
    formulaConstantBits L (tupleCallMomentFormula c hs w walk j f sigma) := by
  apply cert_moment_constant_bits _ _ _ L (by omega)
  · intro edge
    exact tupleMaskFormula_constant_bits _ _ _ _ L hX
      (fun g=>cert_selected_square_constant_bits (by decide : 0<4) _ edge g L)
  · exact cert_pooled_walk_constant_bits (by decide : 0<4) _ _ L hw
      (fun e=>by cases sigma e <;> decide)

/-- `eq:testX` and `lem:print`, paper/paper.tex: the population source's actual quadratic atom sum
and unary even exponent have no tuple-enumeration factor. -/
theorem populationMoment_syntax {G : ℕ} (selection : Fin G→Bool)
    (edge : Fin 8) (structural : Bool) (k : ℕ) :
    (StagePrint.selectedPopulationMomentFormula (by decide : 0<4) selection edge structural k).size≤
      11*G+2*k+4 ∧
    (StagePrint.selectedPopulationMomentFormula (by decide : 0<4) selection edge structural k).weight≤
      1+2*k*(9*G) := by
  have hs := StageLift.sumList_size_le
    (List.ofFn (StagePrint.selectedSquare (by decide : 0<4) selection edge)) 10 (by
      intro F hF
      obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hF
      exact StageLift.selectedSquare_size_le _ _ _ _)
  have hw := cert_sumList_weight_le
    (List.ofFn (StagePrint.selectedSquare (by decide : 0<4) selection edge)) 8 (by
      intro F hF
      obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hF
      exact cert_selected_square_weight_le _ _ _ _)
  simp only [List.length_ofFn] at hs hw
  have hb : Nat.size (if structural then (1:ℤ) else 0).natAbs≤1 := by cases structural <;> decide
  constructor
  · change 1+((Formula.sumList _).size+2*k+1)+1≤_
    omega
  · change Nat.size (if structural then (1:ℤ) else 0).natAbs+2*k*(Formula.sumList _).weight≤_
    nlinarith only [hw,hb]

end NearQuarticWires.StageCert
