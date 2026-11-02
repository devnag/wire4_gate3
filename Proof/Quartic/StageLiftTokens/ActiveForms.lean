import Proof.Quartic.StageLiftTokens.ActivePair
import Proof.Quartic.StageLiftTokens.Pairs
import Proof.Quartic.StageLiftTokens.FormulaStream

/-!
# Original active and inactive form pairs

`lem:residue` and `lem:print`, paper/paper.tex: the actual call tag controls the exact original form
and target, including every literal zero factor of an absent circuit.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def activeScorePair : St VV MM := activePair scorePair
def activeDigitPair : St VV MM := activePair digitPair

def scorePairScratch : List (Fin VV) := (scoreWalkScratch++scoreTargetScratch)++[vJ]
def digitPairScratch : List (Fin VV) := ((atomOccurrence::digitOccurrenceScratch)++digitTargetScratch)++[vJ]

theorem activeScore_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env targetCircuit=j.val) :
    Hs C activeScorePair a (pairSourceCost E+2) (fun b=>
      b.out=a.out++(toks (requestForm r (j,none))).flatMap tokWord++tokWord (.const (requestTarget r (j,none))) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b scorePairScratch) := by
  classical
  have hy:=scorePair_run C r a E h j hj
  let word := (toks (StagePrint.callWalkFormula r.child.call j (fun _=>1) r.pattern)).flatMap tokWord++
    tokWord (.const (r.residues j % (r.prime^r.child.selected.1.e : ℤ)))
  have hh:=activePair_run C r a E h j hj scorePair (pairSourceCost E) word
    (scoreWalkScratch++scoreTargetScratch) (by unfold pairSourceCost linearSourceCost targetSourceCost; have hp:=Nat.one_le_pow 4 (E+1) (by omega); omega)
    (hy.mono le_rfl (fun b ⟨bo,br,bf,bfr⟩=>⟨by simpa only [List.append_assoc] using bo,br,bf,bfr⟩))
  refine hh.mono le_rfl ?_
  rintro b ⟨bo,br,bf,bfr⟩
  refine ⟨?_,br,bf,bfr⟩
  by_cases hjmem : j∈Builder.circuitSet r.child.call
  · simpa only [if_pos hjmem,word,requestForm,callResidueForm,requestTarget,callResidueTarget,
      List.append_assoc] using bo
  · simpa only [if_neg hjmem,requestForm,callResidueForm,requestTarget,callResidueTarget,
      toks,List.flatMap_singleton,List.append_assoc] using bo

theorem activeDigit_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (row : Fin (r.child.selected.1.J-1+1))
    (hj : a.env targetCircuit=j.val) (hr : a.env requestedChainRow=row.val) :
    Hs C activeDigitPair a (pairSourceCost E+2) (fun b=>
      b.out=a.out++(toks (requestForm r (j,some row))).flatMap tokWord++tokWord (.const (requestTarget r (j,some row))) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b digitPairScratch) := by
  classical
  have hy:=digitPair_run C r a E h j row hj hr
  let word := (toks (StagePrint.callWalkFormula r.child.call j
    (StagePrint.callDigitWeights r.child.call
      (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) r.child.witness j row) r.pattern)).flatMap tokWord++
    tokWord (.const ((r.digits j row % (r.prime^r.child.selected.1.e : ℤ)) % (r.prime:ℤ)))
  have hh:=activePair_run C r a E h j hj digitPair (pairSourceCost E) word
    ((atomOccurrence::digitOccurrenceScratch)++digitTargetScratch)
    (by unfold pairSourceCost linearSourceCost targetSourceCost; have hp:=Nat.one_le_pow 4 (E+1) (by omega); omega)
    (hy.mono le_rfl (fun b ⟨bo,br,bf,bfr⟩=>⟨by simpa only [List.append_assoc] using bo,br,bf,bfr⟩))
  refine hh.mono le_rfl ?_
  rintro b ⟨bo,br,bf,bfr⟩
  refine ⟨?_,br,bf,bfr⟩
  by_cases hjmem : j∈Builder.circuitSet r.child.call
  · simpa only [if_pos hjmem,word,requestForm,callResidueForm,requestTarget,callResidueTarget,
      List.append_assoc] using bo
  · simpa only [if_neg hjmem,requestForm,callResidueForm,requestTarget,callResidueTarget,
      toks,List.flatMap_singleton,List.append_assoc] using bo

end NearQuarticWires.StageLiftTokens
