import Proof.Quartic.StagePrep.SelectedDriver
import Proof.Quartic.Cells.ParametersExecutionWidths

/-!
# Selected preparation at the original-input word width

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- The selected preparation computation of `sec:params`,
paper/paper.tex, executes at the proved cubic
original-input bit scale. Every operand-capacity condition is
derived from the literal parameter rules and input encoding. -/
theorem canonicalPreparation_selected_at_width (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : Cells.ParameterInput) (p : Cells.Parameters) (hs : Cells.ParameterRules x p)
    (B1 L num den w1 w2 : ℕ) (hbn : x.beta.num=num) (hbd : x.beta.den=den)
    (hnv : a.env vN=x.n) (hw1 : a.env vTW1=w1) (hw2 : a.env vTW2=w2)
    (hcount : a.env censusTotal=x.W) (hnumv : a.env vNUM=num) (hdenv : a.env vDEN=den)
    (hG1v : a.env vG1=x.G1) (hG2v : a.env vG2=x.G2)
    (hBv : a.env vB0=NearCubicGates.Close.Counter.B0 x.n)
    (hTag : a.env vTAG=1 ↔ x.pair=true) (ha : a.env vADM=1)
    (hn : x.n≤L) (hb : 1≤x.beta*(x.n:ℚ)^B1)
    (hnumBits : num≤2^L) (hdenBits : den≤2^L)
    (hw1Bits : w1≤2^L) (hw2Bits : w2≤2^L)
    (hwidth : 100*Cells.ParameterArithmetic.preparationBitBase B1 L≤C.Wd) :
    Hs C canonicalPreparation a (selectedPreparationCost x p num den) (fun b =>
      RegisterValues b (parameterMemoryValues p) ∧ b.env vADM=1 ∧
      firstRatio p.ell0 p.h p.T=(b.env pXN:ℚ)/b.env pXD ∧
      0<b.env pXN ∧ b.env pXN≤b.env pXD ∧ b.env pXD≤(p.h+32)*b.env pXN ∧
      b.env pXD<2^(5*(Cells.ParameterArithmetic.preparationBitBase B1 L+1)+22) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ FrS a b selectedPreparationT) := by
  have hu : 0<num := by
    have hpos := Rat.num_pos.mpr (Cells.ParameterRules.beta_pos hs)
    rw [hbn] at hpos
    exact_mod_cast hpos
  have hd : 0<den := by rw [←hbd]; exact x.beta.den_pos
  exact canonicalPreparation_selected_spec C a hc x p hs num den w1 w2
    (Cells.ParameterArithmetic.preparationBitBase B1 L+1) hbn hbd hnv hw1 hw2
    hcount hnumv hdenv hG1v hG2v hBv hTag ha
    (hs.selected_widths B1 L num den w1 w2 hn hb hbn hbd hu hd hnumBits hdenBits
      hw1Bits hw2Bits C hwidth)

end NearQuarticWires.StagePrep
