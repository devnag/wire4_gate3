import Proof.Quartic.StagePrep.SelectedAtWidth
import Proof.Quartic.StagePrep.RejectedAtWidth
import Proof.Quartic.StagePrep.HeaderFailure
import Proof.Quartic.Cells.ParametersPreparationHeaderBits

/-!
# Every outcome of the finite parameter computation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open Cells.ParameterArithmetic

/-- A single conservative budget for the actual canonical
computation of `sec:params`, paper/paper.tex.
The initial rejection executes no later public-scale loop. -/
def canonicalPreparationBudget (x : Cells.ParameterInput) (num den : ℕ) : ℕ :=
  if 4*(16*NearCubicGates.Target.mu x.n)≤x.n then
    selectedPreparationCost x (attemptPublicParameters x (Cells.publicScales x)) num den
  else 20*x.n+300

/-- On any successful selection in `sec:params`,
paper/paper.tex, the common budget is exactly
the sum for that actual complete selected record. -/
theorem canonicalPreparationBudget_of_some (x : Cells.ParameterInput)
    (num den : ℕ) (p : Cells.Parameters) (hp : Cells.prepare x=some p) :
    canonicalPreparationBudget x num den=selectedPreparationCost x p num den := by
  have hs := Cells.prepare_spec x p hp
  have hr : 4*(16*NearCubicGates.Target.mu x.n)≤x.n := by
    simpa only [←hs.mu_eq,←hs.r_eq] using hs.r_bound
  rw [canonicalPreparationBudget,if_pos hr,←prepare_some_eq_attempt x hs.input_valid hr p hp]

/-- Every rejected canonical selection in `sec:params`,
paper/paper.tex, is executed with zero final
admission flag and unchanged input cursors. The word capacity
is derived from the original input encoding, including paths
that fail before later parameter identities could be selected. -/
theorem canonicalPreparation_none_at_width (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : Cells.ParameterInput) (hv : ValidInput x) (B1 L num den w1 w2 : ℕ)
    (hbn : x.beta.num=num) (hbd : x.beta.den=den)
    (hnv : a.env vN=x.n) (hw1 : a.env vTW1=w1) (hw2 : a.env vTW2=w2)
    (hcount : a.env censusTotal=x.W) (hnumv : a.env vNUM=num) (hdenv : a.env vDEN=den)
    (hG1v : a.env vG1=x.G1) (hG2v : a.env vG2=x.G2)
    (hBv : a.env vB0=NearCubicGates.Close.Counter.B0 x.n)
    (hTag : a.env vTAG=1 ↔ x.pair=true) (ha : a.env vADM=1)
    (hn : x.n≤L) (hb : 1≤x.beta*(x.n:ℚ)^B1)
    (hnumBits : num≤2^L) (hdenBits : den≤2^L)
    (hw1Bits : w1≤2^L) (hw2Bits : w2≤2^L)
    (hwidth : 100*preparationBitBase B1 L≤C.Wd) (hp : Cells.prepare x=none) :
    Hs C canonicalPreparation a (canonicalPreparationBudget x num den) (fun b =>
      b.env vADM=0 ∧ b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b) := by
  by_cases hr : 4*(16*NearCubicGates.Target.mu x.n)≤x.n
  · rw [canonicalPreparationBudget,if_pos hr]
    let p := attemptPublicParameters x (Cells.publicScales x)
    have hs : AttemptRules x p :=
      attemptPublicParameters_rules x (Cells.publicScales x) (Cells.publicScales_core x hv hr)
    have hfail : ¬attemptPass x p := (prepare_none_iff_attempt_failure x hv hr).mp hp
    exact canonicalPreparation_rejected_at_width C a hc x p hs B1 L num den w1 w2 hbn hbd
      hnv hw1 hw2 hcount hnumv hdenv hG1v hG2v hBv hTag ha hn hb hnumBits hdenBits
      hw1Bits hw2Bits hwidth hfail
  · rw [canonicalPreparationBudget,if_neg hr]
    have hheader := preparationHeader_operand_binary_bound B1 L x.n w1 w2 hn hw1Bits hw2Bits
    exact canonicalPreparation_header_failure C a hc x.n w1 w2 hnv hw1 hw2 ha hr
      (hheader.trans_le (Nat.pow_le_pow_right (by norm_num) hwidth))

end NearQuarticWires.StagePrep
