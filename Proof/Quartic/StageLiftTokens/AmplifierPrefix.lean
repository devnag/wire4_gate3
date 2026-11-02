import Proof.Quartic.StageLiftTokens.FermatRun
import Proof.Quartic.StageLiftTokens.AmplifierLeaves

/-!
# The initial BT factor

`imp:amp` and `lem:print`, paper/paper.tex: the source physically emits the outer unit and the factor
`(1-T)^e`, replaying the actual complete Fermat source for T and reading
the exponent from its retained field.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats StageLift

variable {B1 B2 : ℕ}

def amplifierPrefix : St VV MM :=
  .seq (emitOperator (.const 1)) (.seq (emitOperator (.const 1))
    (.seq fermatProgram (.seq (emitOperator .sub) (emitPower degreeExponent))))

def amplifierPrefixCost (E J : ℕ) : ℕ := fermatSourceCost E J+40*sourceBits E+120

theorem amplifierPrefix_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C amplifierPrefix a (amplifierPrefixCost E r.child.selected.1.J) (fun b=>
      b.out=a.out++tokWord (.const 1)++tokWord (.const 1)++(toks (requestFermat r)).flatMap tokWord++
        tokWord .sub++tokWord (.pow r.child.selected.1.e) ∧
      SourceReady C r b E ∧ SourceFrame a b) := by
  unfold amplifierPrefix
  apply Hx.hs
  refine Hs.then (emitOperator_ready C r a E h (.const 1))
    (fun b ⟨bo,br,bf,_⟩ n1 hn1=>?_)
  refine Hs.then (emitOperator_ready C r b E br (.const 1))
    (fun d ⟨doo,dr,df,_⟩ n2 hn2=>?_)
  refine Hs.then (fermatProgram_run C r d E dr)
    (fun e ⟨eo,er,ef,_⟩ n3 hn3=>?_)
  refine Hs.then (emitOperator_ready C r e E er .sub)
    (fun f ⟨fo,fr,ff,_⟩ n4 hn4=>?_)
  refine Hs.last (emitPower_ready C r f E fr degreeExponent (by decide) (by decide)
    (by rw [fr.exponent]; exact fr.exponent_bound))
    (fun z ⟨zo,zr,zf,_⟩ n5 hn5=>?_)
  refine ⟨⟨?_,zr,bf.trans (df.trans (ef.trans (ff.trans zf)))⟩,?_⟩
  · rw [zo,fo,eo,doo,bo,fr.exponent]
  · have h1 : (tokWord (.const 1)).length=9 := by decide
    have hs : (tokWord .sub).length=7 := by decide
    rw [h1] at hn1 hn2
    rw [hs] at hn4
    unfold amplifierPrefixCost
    omega

end NearQuarticWires.StageLiftTokens
