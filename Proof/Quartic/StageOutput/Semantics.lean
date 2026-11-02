import Proof.Quartic.StageOutput.PaddingDispatch
import Proof.Quartic.StageOutput.Numerators
import Proof.Quartic.Cells.ParametersOutputArithmetic
import Proof.Quartic.Cells.ParametersOutputRounding

/-!
# The exact scalar meaning of Step 5

Paper: `sec:algorithm`, paper/paper.tex. The parsed
sign-magnitude fields give the lower floor and upper ceiling over their
common positive denominator. Their sum and difference are the nonnegative
integer numerators of the reported center and radius.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

noncomputable def selectedInput (c : Call) (p : Program.Selected c) (w : List Bool) : Input :=
  { n := c.n, k := p.1.k, Q := p.1.Q, MF := p.1.MF,
    etaNum := p.1.eta.num.natAbs, etaDen := p.1.eta.den,
    nc := (Program.runCall c p w).certifiedColumns.card,
    consistent := Program.consistentBit (Program.runCall c p w),
    A := (Program.acceptTotal (Program.runCall c p w)).natAbs,
    M := (Program.maskTotal (Program.runCall c p w)).natAbs }

noncomputable def outputRequest (B1 B2 : ℕ) (c : Call) (w : List Bool) : OutputRequest :=
  match Program.dispatch B1 B2 c with
  | none => .inl (Program.admittedValue B1 B2 Builder.value c w)
  | some p => .inr (selectedInput c p w)

theorem outputRequest_word (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (outputRequest B1 B2 c w).word = Program.mainWord B1 B2 c w := by
  classical
  unfold outputRequest Program.mainWord Program.stageWord
  split
  · rename_i hd
    rw [hd]
    rfl
  · rename_i p hd
    rw [hd]
    have hb := Cells.selected_output_bounds c p w
    have he := Rat.num_nonneg.mpr hb.2.2.1
    have ha := hb.2.2.2.2.1
    have hm := le_trans ha hb.2.2.2.2.2.1
    cases hbool : Program.consistentBit (Program.runCall c p w) <;>
      simp [hbool, OutputRequest.word, selectedInput, Input.word, Input.fields, ratWord,
      NearCubicGates.Close.Interfaces.intWord, bitWord, Bool.toNat, not_lt.mpr he, not_lt.mpr ha, not_lt.mpr hm, List.append_assoc]

def Input.floorValue (d : Input) : ℤ :=
  differenceRound false d.lowerPositive d.lowerNegative d.denominator

def Input.ceilValue (d : Input) : ℤ :=
  differenceRound true d.upperPositive d.upperNegative d.denominator

def Input.centerNumerator (d : Input) : ℕ := (d.floorValue + d.ceilValue).natAbs
def Input.radiusNumerator (d : Input) : ℕ := (d.ceilValue - d.floorValue).natAbs

def Input.result (d : Input) : ℚ × ℚ :=
  if d.consistent then
    ((d.centerNumerator : ℚ) / (2 ^ (d.n + 1) : ℕ),
     (d.radiusNumerator : ℚ) / (2 ^ (d.n + 1) : ℕ))
  else Algorithm.soundDefault

theorem selectedInput_rounding (c : Call) (p : Program.Selected c) (w : List Bool) :
    (selectedInput c p w).floorValue =
      ⌊Program.stepFiveLower c.n p.1 (Program.acceptTotal (Program.runCall c p w))
        (Program.runCall c p w).certifiedColumns.card * 2 ^ c.n⌋ ∧
    (selectedInput c p w).ceilValue =
      ⌈Program.stepFiveUpper c.n p.1 (Program.acceptTotal (Program.runCall c p w))
        (Program.maskTotal (Program.runCall c p w))
        (Program.runCall c p w).certifiedColumns.card * 2 ^ c.n⌉ := by
  have hb := Cells.selected_output_bounds c p w
  have hM := hb.2.2.2.2.1.trans hb.2.2.2.2.2.1
  have hD := Cells.outputDenominator_pos p.1 hb.1
  have hf := Cells.stepFiveLower_integer_fraction c.n p.1
    (Program.acceptTotal (Program.runCall c p w))
    (Program.runCall c p w).certifiedColumns.card hb.2.1 hb.1 hb.2.2.1 hb.2.2.2.2.1
  have hg := Cells.stepFiveUpper_integer_fraction c.n p.1
    (Program.acceptTotal (Program.runCall c p w)) (Program.maskTotal (Program.runCall c p w))
    (Program.runCall c p w).certifiedColumns.card hb.2.1 hb.1 hb.2.2.1 hb.2.2.2.2.1 hM
  have hD' : 0 < (selectedInput c p w).denominator := hD
  constructor
  · rw [Input.floorValue, differenceRound_floor _ _ _ hD', hf]
    push_cast
    rfl
  · rw [Input.ceilValue, differenceRound_ceil _ _ _ hD', hg]
    push_cast
    rfl

theorem selectedInput_nonneg (c : Call) (p : Program.Selected c) (w : List Bool) :
    0 ≤ (selectedInput c p w).ceilValue ∧
    0 ≤ (selectedInput c p w).floorValue + (selectedInput c p w).ceilValue ∧
    0 ≤ (selectedInput c p w).ceilValue - (selectedInput c p w).floorValue := by
  have hb := Cells.selected_output_bounds c p w
  have he := Cells.stepFive_endpoint_bounds c.n p.1
    (Program.acceptTotal (Program.runCall c p w)) (Program.maskTotal (Program.runCall c p w))
    (Program.runCall c p w).certifiedColumns.card hb.1 hb.2.2.1 hb.2.2.2.2.1
    hb.2.2.2.2.2.1 hb.2.2.2.2.2.2 hb.2.2.2.1
  rw [(selectedInput_rounding c p w).1, (selectedInput_rounding c p w).2]
  exact Cells.rounded_output_numerators_nonneg _ _ _ he.1 he.2.1 he.2.2

/-- The exact ordinary scalar computation returns the value specified in Step 5. -/
theorem selectedInput_result {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (selectedInput c p w).result = Program.admittedValue B1 B2 Builder.value c w := by
  classical
  rw [Program.dispatched_value hd w]
  unfold Input.result
  have hcon : (selectedInput c p w).consistent = decide (Program.runCall c p w).PathConsistent := rfl
  rw [hcon]
  simp only [decide_eq_true_eq]
  split_ifs
  · apply Prod.ext
    · dsimp only [Prod.fst]
      have h := Machine.roundedInterval_center_scaled c.n
        (Program.stepFiveLower c.n p.1 (Program.acceptTotal (Program.runCall c p w))
          (Program.runCall c p w).certifiedColumns.card)
        (Program.stepFiveUpper c.n p.1 (Program.acceptTotal (Program.runCall c p w))
          (Program.maskTotal (Program.runCall c p w)) (Program.runCall c p w).certifiedColumns.card)
      have hn := (selectedInput_nonneg c p w).2.1
      rw [Input.centerNumerator, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hn]
      rw [(selectedInput_rounding c p w).1, (selectedInput_rounding c p w).2]
      apply (div_eq_iff (by positivity)).mpr
      simpa only [selectedInput, Nat.cast_pow, Nat.cast_ofNat, Machine.roundedInterval,
        Machine.dyadicFloor, Machine.dyadicCeil, Algorithm.centerRadius, Algorithm.dyadicFloor,
        Algorithm.dyadicCeil] using h.symm
    · dsimp only [Prod.snd]
      have h := Machine.roundedInterval_radius_scaled c.n
        (Program.stepFiveLower c.n p.1 (Program.acceptTotal (Program.runCall c p w))
          (Program.runCall c p w).certifiedColumns.card)
        (Program.stepFiveUpper c.n p.1 (Program.acceptTotal (Program.runCall c p w))
          (Program.maskTotal (Program.runCall c p w)) (Program.runCall c p w).certifiedColumns.card)
      have hn := (selectedInput_nonneg c p w).2.2
      rw [Input.radiusNumerator, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg hn]
      rw [(selectedInput_rounding c p w).1, (selectedInput_rounding c p w).2]
      apply (div_eq_iff (by positivity)).mpr
      simpa only [selectedInput, Nat.cast_pow, Nat.cast_ofNat, Machine.roundedInterval,
        Machine.dyadicFloor, Machine.dyadicCeil, Algorithm.centerRadius, Algorithm.dyadicFloor,
        Algorithm.dyadicCeil] using h.symm
  · rfl

end NearQuarticWires.StageOutput
