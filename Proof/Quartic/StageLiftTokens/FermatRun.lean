import Proof.Quartic.StageLiftTokens.FermatSyntax
import Proof.Quartic.StageLiftTokens.ProductCloser

/-!
# The actual full Fermat source

`lem:residue` and `lem:print`, paper/paper.tex: the concrete nested circuit and digit loops, followed
by the actual computed product closure, emit the complete original
Fermat formula and retain the amplifier ordinal for exact replay.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats StageLift

variable {B1 B2 : ℕ}

def fermatProgram : St VV MM := .seq allFactorsProgram productCloser

def fermatSourceCost (E J : ℕ) : ℕ := allFactorCost E J+productCloserCost J+1

theorem fermatProgram_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C fermatProgram a (fermatSourceCost E r.child.selected.1.J) (fun b=>
      b.out=a.out++(toks (requestFermat r)).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ b.env amplifierIndex=a.env amplifierIndex) := by
  unfold fermatProgram fermatSourceCost
  refine Hs.seq (allFactorsProgram_run C r a E h) ?_
  rintro b ⟨bo,br,bf,bi⟩
  refine (productCloser_run C r b E br).mono le_rfl ?_
  rintro d ⟨doo,dr,df,di⟩
  refine ⟨?_,dr,bf.trans df,di.trans bi⟩
  rw [doo,bo,requestFermat_tokens]
  simp only [List.append_assoc]

end NearQuarticWires.StageLiftTokens
