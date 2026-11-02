import Proof.Quartic.StageLiftTokens.AmplifierPrefix

/-!
# One actual BT summand

`imp:amp` and `lem:print`, paper/paper.tex: each live ordinal computes its full integer binomial,
replays the original Fermat source, and emits the power and product.
The ordinal survives the complete source replay.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageLift

variable {B1 B2 : ℕ}

noncomputable def amplifierTermFormula (r : Greedy.PrintRequest B1 B2) (j : ℕ) :=
  Formula.mul (.const (((r.child.selected.1.e-1+j).choose j:ℕ):ℤ)) (.pow (requestFermat r) j)

def amplifierTerm : St VV MM :=
  .seq emitAmplifierCoefficient (.seq fermatProgram
    (.seq (emitPower amplifierIndex) (emitOperator .mul)))

def amplifierTermCost (E J : ℕ) : ℕ := fermatSourceCost E J+17*E+80*sourceBits E+160

theorem amplifierTerm_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin r.child.selected.1.e) (hj : a.env amplifierIndex=j.val) :
    Hs C amplifierTerm a (amplifierTermCost E r.child.selected.1.J) (fun b=>
      b.out=a.out++(toks (amplifierTermFormula r j.val)).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ b.env amplifierIndex=j.val) := by
  unfold amplifierTerm
  apply Hx.hs
  refine Hs.then (emitCoefficient_ready C r a E h j hj)
    (fun b ⟨bo,br,bf,bfr⟩ n1 hn1=>?_)
  have bi : b.env amplifierIndex=j.val := (bfr _ (by decide)).trans hj
  refine Hs.then (fermatProgram_run C r b E br)
    (fun d ⟨doo,dr,df,di⟩ n2 hn2=>?_)
  have didx : d.env amplifierIndex=j.val := di.trans bi
  refine Hs.then (emitPower_ready C r d E dr amplifierIndex (by decide) (by decide)
    (by rw [didx]; exact j.isLt.le.trans h.exponent_bound))
    (fun e ⟨eo,er,ef,efr⟩ n3 hn3=>?_)
  refine Hs.last (emitOperator_ready C r e E er .mul)
    (fun z ⟨zo,zr,zf,zfr⟩ n4 hn4=>?_)
  refine ⟨⟨?_,zr,bf.trans (df.trans (ef.trans zf)),
    (zfr _ (by decide)).trans ((efr _ (by decide)).trans didx)⟩,?_⟩
  · rw [zo,eo,doo,bo,didx]
    simp only [amplifierTermFormula,toks,List.flatMap_append,List.flatMap_singleton,List.append_assoc]
  · have hm : (tokWord .mul).length=7 := by decide
    rw [hm] at hn4
    have hjE := j.isLt.le.trans h.exponent_bound
    unfold amplifierTermCost
    omega

end NearQuarticWires.StageLiftTokens
