import Proof.Quartic.StageLiftMasks.Edge
import Proof.Quartic.StageLiftMasks.Token

/-!
# Ordered product of the eight actual edge masks

`lem:maskpoly` and `lem:print`, paper/paper.tex: each original edge contributes its
complete mask formula in walk order. Literal multiplication follows
the right-associated finite product, whose empty value is one.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

def printMaskList : List (Fin 8)→St VV MM
  | [] =>emitOperator (.const 1)
  | edge::edges =>.seq (edgeProgram edge) (.seq (printMaskList edges) (emitOperator .mul))

theorem printMaskList_run {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (edges : List (Fin 8)) (a : DS VV MM) (h : PrintMasksReady width input L B r index a) :
    Hs (structuralSourceContext B1 B2 width input L B) (printMaskList edges) a
      (edges.length*(edgeCost r L B+20)+20) (fun b=>
        b.out=a.out++(toks (maskProductFormula r index edges)).flatMap tokWord ∧
        PrintMasksReady width input L B r index b ∧ MaskFrame a b) := by
  induction edges generalizing a with
  | nil =>
    refine (emitOperator_ready input r index a h (.const 1)).mono
      (by
        have hh : (tokWord (.const 1)).length=9 := by decide
        rw [hh]
        simp) ?_
    rintro b ⟨bo,br,bf⟩
    exact ⟨by simpa [maskProductFormula,Mask.formulaListProd,toks] using bo,br,bf⟩
  | cons edge edges ih =>
    unfold printMaskList
    apply Hx.hs
    refine Hs.then (edgeProgram_run input r index edge a h)
      (fun b ⟨bo,br,bf⟩ n1 hn1=>?_)
    refine Hs.then (ih b br) (fun d ⟨doo,dr,df⟩ n2 hn2=>?_)
    refine Hs.last (emitOperator_ready input r index d dr .mul)
      (fun z ⟨zo,zr,zf⟩ n3 hn3=>?_)
    refine ⟨⟨?_,zr,bf.trans (df.trans zf)⟩,?_⟩
    · rw [zo,doo,bo]
      simp only [maskProductFormula,List.map_cons,Mask.formulaListProd,toks,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    · have hm : (tokWord .mul).length=7 := by decide
      rw [hm] at hn3
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

end NearQuarticWires.StageLiftMasks
