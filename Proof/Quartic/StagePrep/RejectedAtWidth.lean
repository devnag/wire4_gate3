import Proof.Quartic.StagePrep.RejectedDriver
import Proof.Quartic.Cells.ParametersAttemptWidths
import Proof.Quartic.Cells.ParametersFailureWindows

/-!
# Rejected preparation at the original-input word width

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The rejected computation in `sec:params`,
paper/paper.tex, executes at the proved
original-input bit scale. Every capacity follows from early
public identities and generic finite scan bounds. -/
theorem canonicalPreparation_rejected_at_width (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : Cells.ParameterInput) (p : Cells.Parameters) (hs : AttemptRules x p)
    (B1 L num den w1 w2 : ℕ) (hbn : x.beta.num=num) (hbd : x.beta.den=den)
    (hnv : a.env vN=x.n) (hw1 : a.env vTW1=w1) (hw2 : a.env vTW2=w2)
    (hcount : a.env censusTotal=x.W) (hnumv : a.env vNUM=num) (hdenv : a.env vDEN=den)
    (hG1v : a.env vG1=x.G1) (hG2v : a.env vG2=x.G2)
    (hBv : a.env vB0=NearCubicGates.Close.Counter.B0 x.n)
    (hTag : a.env vTAG=1 ↔ x.pair=true) (ha : a.env vADM=1)
    (hn : x.n≤L) (hb : 1≤x.beta*(x.n:ℚ)^B1)
    (hnumBits : num≤2^L) (hdenBits : den≤2^L)
    (hw1Bits : w1≤2^L) (hw2Bits : w2≤2^L)
    (hwidth : 100*Cells.ParameterArithmetic.preparationBitBase B1 L≤C.Wd)
    (hfail : ¬attemptPass x p) :
    Hs C canonicalPreparation a (selectedPreparationCost x p num den) (fun b =>
      b.env vADM=0 ∧ b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b) := by
  have hs0 := hs.toCoreRules
  have hu : 0<num := by
    have hpos := Rat.num_pos.mpr hs0.beta_pos
    rw [hbn] at hpos
    exact_mod_cast hpos
  have hd : 0<den := by rw [←hbd]; exact x.beta.den_pos
  have hP : p.P≤x.n := by rw [hs.P_eq]; exact Nat.findGreatest_le _
  have hD : p.Dprime≤(x.n+1)^2 := by
    rw [hs.Dprime_eq,hs.primes_eq]
    exact (Cells.ParameterArithmetic.scan_windows_le_arity_square x.n p.P hP x.pair).1
  have hh : p.h≤x.n := by
    rw [hs.h_eq,hs.hE_eq]
    exact (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hP)
  exact canonicalPreparation_rejected_spec C a hc x p hs num den w1 w2
    (Cells.ParameterArithmetic.preparationBitBase B1 L+1) hbn hbd hnv hw1 hw2
    hcount hnumv hdenv hG1v hG2v hBv hTag ha
    (hs0.attempt_widths B1 L num den w1 w2 hn hb hbn hbd hu hd hnumBits hdenBits
      hw1Bits hw2Bits hP hD hh C hwidth) hfail

end NearQuarticWires.StagePrep
