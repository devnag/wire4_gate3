import Proof.Quartic.StageLiftTokens.LinearRun
import Proof.Quartic.StageLiftTokens.DigitTarget

/-!
# Form and target token pairs

`lem:residue` and `lem:print`, paper/paper.tex: each real original form is followed by its real normalized
target token, in the same circuit and chain-row order as the Fermat product.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def scorePair : St VV MM := .seq emitScoreWalkForm scoreTargetProgram
def digitPair : St VV MM := .seq (emitDigitWalkForm witnessStore factorStore) digitTargetProgram

def pairSourceCost (E : ℕ) : ℕ := linearSourceCost E+targetSourceCost E+1

theorem scorePair_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env targetCircuit=j.val) :
    Hs C scorePair a (pairSourceCost E) (fun b=>
      b.out=a.out++(toks (StagePrint.callWalkFormula r.child.call j (fun _=>1) r.pattern)).flatMap tokWord++
        tokWord (.const (r.residues j % (r.prime^r.child.selected.1.e : ℤ))) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (scoreWalkScratch++scoreTargetScratch)) := by
  unfold scorePair pairSourceCost
  refine Hs.seq (emitScore_ready C r a E h j hj) ?_
  rintro b ⟨bo,br,bf,bfr⟩
  refine (scoreTarget_run C r b E br j ((bfr _ (by decide)).trans hj)).mono le_rfl ?_
  rintro d ⟨doo,dr,df,dfr⟩
  exact ⟨by rw [doo,bo],dr,bf.trans df,
    (bfr.weaken (by intro x hx; exact List.mem_append_left _ hx)).trans
      (dfr.weaken (by intro x hx; exact List.mem_append_right _ hx))⟩

theorem digitPair_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (row : Fin (r.child.selected.1.J-1+1))
    (hj : a.env targetCircuit=j.val) (hr : a.env requestedChainRow=row.val) :
    Hs C digitPair a (pairSourceCost E) (fun b=>
      b.out=a.out++(toks (StagePrint.callWalkFormula r.child.call j
        (StagePrint.callDigitWeights r.child.call
          (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) r.child.witness j row) r.pattern)).flatMap tokWord++
        tokWord (.const ((r.digits j row % (r.prime^r.child.selected.1.e : ℤ)) % (r.prime:ℤ))) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧
      Fr a b ((atomOccurrence::digitOccurrenceScratch)++digitTargetScratch)) := by
  unfold digitPair pairSourceCost
  refine Hs.seq (emitDigit_ready C r a E h j row hj hr) ?_
  rintro b ⟨bo,br,bf,bfr⟩
  refine (digitTarget_run C r b E br j row ((bfr _ (by decide)).trans hj)
    ((bfr _ (by decide)).trans hr)).mono le_rfl ?_
  rintro d ⟨doo,dr,df,dfr⟩
  exact ⟨by rw [doo,bo],dr,bf.trans df,
    (bfr.weaken (by intro x hx; exact List.mem_append_left _ hx)).trans
      (dfr.weaken (by intro x hx; exact List.mem_append_right _ hx))⟩

end NearQuarticWires.StageLiftTokens
