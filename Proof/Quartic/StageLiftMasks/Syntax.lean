import Proof.Quartic.StageLiftMasks.Request
import Proof.Quartic.StageLiftTokens.WitnessDock

/-!
# Exact original tuple-mask syntax

`lem:maskpoly` and `lem:print`, paper/paper.tex: the retained witness gives the original
occurrence selection and the eight guarded-tuple factors have exactly
the original walk-product order.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

theorem retained_selection (c : Call) (p : Cells.Parameters) (w : List Bool) :
    (fun i : Fin (Builder.allGates c).length=>
      (Program.witnessPrefix c p w).getD (p.k+i.val) false)=Builder.selection c (p:=p) w := by
  funext i
  apply Program.witnessBit_witnessPrefix c p w
  have hlen : (Builder.allGates c).length=Builder.occurrences c 0+Builder.occurrences c 1 := by
    simp [Builder.allGates,Builder.occurrences,Builder.gatesOf]
  have hg : (Builder.allGates c).length≤(p.J+1)*(Builder.allGates c).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold Program.witnessReadLength
  have hi:=i.isLt
  rw [←hlen]
  omega

noncomputable def edgeMaskFormula (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    Formula (17*(Builder.allGates r.child.call).length) :=
  StageCert.tupleMaskFormula
    (StagePrint.callStructural r.child.call
      (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge)
    (StagePrint.selectedSquare (by decide : 0<4)
      (Builder.selection r.child.call (p:=r.child.selected.1) r.child.witness) edge)
    r.child.selected.1.tau r.child.selected.1.Xmax

noncomputable def maskProductFormula (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edges : List (Fin 8)) :
    Formula (17*(Builder.allGates r.child.call).length) :=
  Mask.formulaListProd (edges.map (edgeMaskFormula r index))

theorem maskProductFormula_full (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) :
    maskProductFormula r index (List.ofFn fun edge : Fin 8=>edge)=printMasksFormula r index := by
  unfold maskProductFormula printMasksFormula Cells.walkMaskFormula
  rw [formula_prodList_eq]
  simp only [List.map_ofFn,Function.comp_def]
  rfl

end NearQuarticWires.StageLiftMasks
