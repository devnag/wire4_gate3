import Proof.Quartic.StageLiftTokens.AmplifierTerm

/-!
# Literal amplifier syntax

`imp:amp` and `lem:print`, paper/paper.tex: the original ordered binomial sum has exactly the token
stream emitted by the exponent-indexed physical loop.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

variable {B1 B2 : ℕ}

theorem ofFn_nat_eq_map_range {α : Type*} (n : ℕ) (f : ℕ → α) :
    (List.ofFn fun j : Fin n => f j.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]

theorem amp_tokens {V : ℕ} (e : ℕ) (t : Formula V) :
    (toks (Formula.amp e t)).flatMap tokWord =
      tokWord (.const 1)++tokWord (.const 1)++(toks t).flatMap tokWord++
      tokWord .sub++tokWord (.pow e)++
      ((List.range e).map fun j =>
        (toks (Formula.mul (.const (((e-1+j).choose j:ℕ):ℤ)) (.pow t j))).flatMap tokWord).flatten++
      tokWord (.const 0)++(List.replicate e .add).flatMap tokWord++
      tokWord .mul++tokWord .sub := by
  simp only [Formula.amp,toks,StageCert.Tokens.originalSumList_tokens,
    List.flatMap_append,List.flatMap_singleton,List.length_map,List.length_range,
    List.flatMap_assoc,List.flatMap_map,List.append_assoc]
  rfl

theorem amplifier_tokens (r : Greedy.PrintRequest B1 B2) :
    (toks (Formula.amp r.child.selected.1.e (requestFermat r))).flatMap tokWord =
      tokWord (.const 1)++tokWord (.const 1)++(toks (requestFermat r)).flatMap tokWord++
      tokWord .sub++tokWord (.pow r.child.selected.1.e)++
      (List.ofFn fun j : Fin r.child.selected.1.e =>
        (toks (amplifierTermFormula r j.val)).flatMap tokWord).flatten++
      tokWord (.const 0)++(List.replicate r.child.selected.1.e .add).flatMap tokWord++
      tokWord .mul++tokWord .sub := by
  rw [ofFn_nat_eq_map_range r.child.selected.1.e
    (fun j=>(toks (amplifierTermFormula r j)).flatMap tokWord)]
  exact amp_tokens r.child.selected.1.e (requestFermat r)

end NearQuarticWires.StageLiftTokens
