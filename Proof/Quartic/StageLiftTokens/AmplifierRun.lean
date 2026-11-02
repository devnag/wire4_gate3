import Proof.Quartic.StageLiftTokens.AmplifierSyntax
import Proof.Quartic.StageLiftTokens.AmplifierTail

/-!
# Physical amplified residue stream

`imp:amp`, `lem:residue` and `lem:print`, paper/paper.tex: the actual integer binomial loop and
original-source replays emit the complete amplified residue formula.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageLift

variable {B1 B2 : ℕ}

def amplifierProgram : St VV MM :=
  .seq amplifierPrefix (.seq amplifierLoop amplifierTail)

def amplifierSourceCost (E J e : ℕ) : ℕ :=
  amplifierPrefixCost E J+amplifierLoopCost E J e+amplifierTailCost e+2

theorem amplifierProgram_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C amplifierProgram a
      (amplifierSourceCost E r.child.selected.1.J r.child.selected.1.e) (fun b=>
      b.out=a.out++(toks (residueBodyFormula r)).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b) := by
  unfold amplifierProgram
  apply Hx.hs
  refine Hs.then (amplifierPrefix_run C r a E h)
    (fun b ⟨bo,br,bf⟩ n1 hn1=>?_)
  refine Hs.then (amplifierLoop_run C r b E br)
    (fun d ⟨doo,dr,df⟩ n2 hn2=>?_)
  refine Hs.last (amplifierTail_run C r d E dr)
    (fun z ⟨zo,zr,zf⟩ n3 hn3=>?_)
  refine ⟨⟨?_,zr,bf.trans (df.trans zf)⟩,?_⟩
  · rw [zo,doo,bo,residueBodyFormula_eq,amplifier_tokens]
    simp only [List.append_assoc]
  · unfold amplifierSourceCost
    omega

end NearQuarticWires.StageLiftTokens
