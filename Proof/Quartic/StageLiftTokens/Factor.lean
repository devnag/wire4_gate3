import Proof.Quartic.StageLiftTokens.ActiveForms

/-!
# Physical original Fermat factors

`lem:residue` and `lem:print`, paper/paper.tex: each factor prints one, its actual form and target,
their subtraction, the computed prime-minus-one exponent, and the
final subtraction. No factor value or formula word is supplied.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def factorProgram (pair : St VV MM) : St VV MM :=
  .seq (emitOperator (.const 1)) (.seq pair (.seq (emitOperator .sub) finishFermatFactor))

def factorScratch (T : List (Fin VV)) : List (Fin VV) := [vJ]++T++(targetValue::tokenScratch)

theorem factorProgram_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (i : Fin 2 × Option (Fin (r.child.selected.1.J-1+1)))
    (pair : St VV MM) (t : ℕ) (T : List (Fin VV))
    (hp : ∀b,SourceReady C r b E→Fr a b [vJ]→
      Hs C pair b t (fun d=>
        d.out=b.out++(toks (requestForm r i)).flatMap tokWord++tokWord (.const (requestTarget r i)) ∧
        SourceReady C r d E ∧ SourceFrame b d ∧ Fr b d T)) :
    Hs C (factorProgram pair) a (t+40*sourceBits E+130) (fun b=>
      b.out=a.out++(toks (requestFactor r i)).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (factorScratch T)) := by
  unfold factorProgram
  apply Hx.hs
  refine Hs.then (emitOperator_ready C r a E h (.const 1))
    (fun b ⟨bo,br,bf,bfr⟩ n1 hn1=>?_)
  refine Hs.then (hp b br bfr) (fun d ⟨doo,dr,df,dfr⟩ n2 hn2=>?_)
  refine Hs.then (emitOperator_ready C r d E dr .sub)
    (fun e ⟨eo,er,ef,efr⟩ n3 hn3=>?_)
  refine Hs.last (finishFermat_ready C r e E er)
    (fun z ⟨zo,zr,zf,zfr⟩ n4 hn4=>?_)
  refine ⟨⟨?_,zr,bf.trans (df.trans (ef.trans zf)),
    (bfr.weaken ?_).trans ((dfr.weaken ?_).trans ((efr.weaken ?_).trans (zfr.weaken ?_)))⟩,?_⟩
  · rw [zo,eo,doo,bo,requestFactor_tokens]
    simp only [List.append_assoc]
  · intro x hx; simp only [factorScratch,List.mem_append,List.mem_cons] at hx ⊢; tauto
  · intro x hx; simp only [factorScratch,List.mem_append,List.mem_cons] at hx ⊢; tauto
  · intro x hx; simp only [factorScratch,List.mem_append,List.mem_cons] at hx ⊢; tauto
  · intro x hx; simp only [factorScratch,List.mem_append,List.mem_cons] at hx ⊢; tauto
  · have h1 : (tokWord (.const 1)).length=9 := by decide
    have hs : (tokWord .sub).length=7 := by decide
    rw [h1] at hn1
    rw [hs] at hn3
    omega

def scoreFactor : St VV MM := factorProgram activeScorePair
def digitFactor : St VV MM := factorProgram activeDigitPair

def factorSourceCost (E : ℕ) : ℕ := pairSourceCost E+40*sourceBits E+132

theorem scoreFactor_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env targetCircuit=j.val) :
    Hs C scoreFactor a (factorSourceCost E) (fun b=>
      b.out=a.out++(toks (requestFactor r (j,none))).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (factorScratch scorePairScratch)) := by
  exact (factorProgram_run C r a E h (j,none) activeScorePair (pairSourceCost E+2)
    scorePairScratch (fun b br bfr=>activeScore_run C r b E br j ((bfr _ (by decide)).trans hj))).mono
      (by unfold factorSourceCost; omega) (fun _ hb=>hb)

theorem digitFactor_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (row : Fin (r.child.selected.1.J-1+1))
    (hj : a.env targetCircuit=j.val) (hr : a.env requestedChainRow=row.val) :
    Hs C digitFactor a (factorSourceCost E) (fun b=>
      b.out=a.out++(toks (requestFactor r (j,some row))).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (factorScratch digitPairScratch)) := by
  exact (factorProgram_run C r a E h (j,some row) activeDigitPair (pairSourceCost E+2)
    digitPairScratch (fun b br bfr=>activeDigit_run C r b E br j row
      ((bfr _ (by decide)).trans hj) ((bfr _ (by decide)).trans hr))).mono
      (by unfold factorSourceCost; omega) (fun _ hb=>hb)

end NearQuarticWires.StageLiftTokens
