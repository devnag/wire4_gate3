import Proof.Quartic.StageLiftTokens.Circuits

/-!
# Original factor order and product syntax

`lem:residue` and `lem:print`, paper/paper.tex: the two physical circuit passes have exactly the
original circuit-major factor order. The trailing unit and closing
multiplications give the literal right-associated Fermat product.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats StageLift

variable {B1 B2 : ℕ}

theorem originalProdList_tokens {V : ℕ} (fs : List (Formula V)) :
    toks (Formula.prodList fs)=fs.flatMap toks++[.const 1]++List.replicate fs.length .mul := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [Formula.prodList,toks,ih,List.flatMap_cons,List.length_cons]
    rw [List.replicate_succ']
    simp only [List.append_assoc]

theorem allFactorWord_eq (r : Greedy.PrintRequest B1 B2) :
    allFactorWord r=((formIndices (r.child.selected.1.J-1)).map (requestFactor r)).flatMap
      (fun f=>(toks f).flatMap tokWord) := by
  simp only [allFactorWord,formIndices,List.flatMap,List.map_flatten,
    List.map_ofFn,Function.comp_def,List.map_cons,List.flatten_cons,List.flatten_flatten]
  rfl

theorem requestFermat_tokens (r : Greedy.PrintRequest B1 B2) :
    (toks (requestFermat r)).flatMap tokWord=allFactorWord r++tokWord (.const 1)++
      (List.replicate (2*(r.child.selected.1.J+1)) .mul).flatMap tokWord := by
  have hJ : r.child.selected.1.J-1+2=r.child.selected.1.J+1 := by
    have hp:=(Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).J_pos
    omega
  change (toks (Formula.prodList ((formIndices (r.child.selected.1.J-1)).map (requestFactor r)))).flatMap tokWord=_
  rw [originalProdList_tokens]
  simp only [List.flatMap_append,List.flatMap_singleton,List.length_map,formIndices_length,hJ]
  rw [List.flatMap_assoc,←allFactorWord_eq]

end NearQuarticWires.StageLiftTokens
