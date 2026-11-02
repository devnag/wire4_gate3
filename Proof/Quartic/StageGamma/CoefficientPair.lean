import Proof.Quartic.StageGamma.ChoicePrepare

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires.WireExponent3_5

/-- `cor:conditional`, paper/paper.tex: a signed
coefficient is physically represented as a difference of two naturals. -/
structure CoefficientPair where
  positive : ℕ
  negative : ℕ

/-- `cor:conditional`, paper/paper.tex: the exact
integer represented by two binary natural coefficient registers. -/
def CoefficientPair.value (p : CoefficientPair) : ℤ :=
  (p.positive : ℤ) - p.negative

/-- `cor:conditional`, paper/paper.tex: a constant
slot scales both signs by Q; a selected sample scales and exchanges them. -/
def CoefficientPair.step (N Q digit : ℕ) (p : CoefficientPair) : CoefficientPair :=
  if digit = 0 then ⟨p.positive * Q, p.negative * Q⟩
  else ⟨p.negative * N ^ 2, p.positive * N ^ 2⟩

/-- `cor:conditional`, paper/paper.tex: the true
radix digit determines the ORIGINAL signed one-slot coefficient. -/
theorem choiceCoefficient_if (N Q : ℕ) (digit : Fin (Q + 1)) :
    Cycle.choiceCoefficient N Q digit =
      if digit.val = 0 then (Q : ℤ) else -(N : ℤ) ^ 2 := by
  refine Fin.cases ?_ (fun j => ?_) digit
  · rfl
  · simp [Cycle.choiceCoefficient]

/-- `cor:conditional`, paper/paper.tex: natural
pair multiplication retains every sign of the exact coefficient expansion. -/
theorem CoefficientPair.step_value (N Q : ℕ) (digit : Fin (Q + 1)) (p : CoefficientPair) :
    (p.step N Q digit.val).value = p.value * Cycle.choiceCoefficient N Q digit := by
  rw [choiceCoefficient_if]
  by_cases hd : digit.val = 0 <;>
    simp [step, value, hd, Nat.cast_mul, Nat.cast_pow] <;> ring

/-- `cor:conditional`, paper/paper.tex: the actual
positive and negative registers have total size equal to their absolute
product bound, without relying on signed cancellation. -/
theorem CoefficientPair.step_mass (N Q : ℕ) (digit : Fin (Q + 1)) (p : CoefficientPair) :
    (p.step N Q digit.val).positive + (p.step N Q digit.val).negative =
      (p.positive + p.negative) * (Cycle.choiceCoefficient N Q digit).natAbs := by
  rw [choiceCoefficient_if]
  by_cases hd : digit.val = 0 <;>
    simp [step, hd, Int.natAbs_neg, Int.natAbs_pow] <;> ring

/-- `cor:conditional`, paper/paper.tex: the finite
choice list determines the actual signed coefficient-pair fold. -/
def coefficientPairFold (N Q : ℕ) (choice : Cycle.GammaChoice Q)
    (slots : List (Fin 8)) (p : CoefficientPair) : CoefficientPair :=
  slots.foldl (fun p slot => p.step N Q (choice slot).val) p

/-- `cor:conditional`, paper/paper.tex: the complete
natural-pair fold is the ORIGINAL signed product for every list of slots. -/
theorem coefficientPairFold_value (N Q : ℕ) (choice : Cycle.GammaChoice Q)
    (slots : List (Fin 8)) (p : CoefficientPair) :
    (coefficientPairFold N Q choice slots p).value = p.value *
      (slots.map (fun slot => Cycle.choiceCoefficient N Q (choice slot))).prod := by
  induction slots generalizing p with
  | nil => simp [coefficientPairFold]
  | cons slot slots ih =>
    simp only [coefficientPairFold, List.foldl_cons]
    rw [← coefficientPairFold, ih, CoefficientPair.step_value]
    simp [mul_assoc]

/-- `cor:conditional`, paper/paper.tex: every
intermediate natural coefficient pair has an explicit uncancelled mass. -/
theorem coefficientPairFold_mass (N Q : ℕ) (choice : Cycle.GammaChoice Q)
    (slots : List (Fin 8)) (p : CoefficientPair) :
    (coefficientPairFold N Q choice slots p).positive +
        (coefficientPairFold N Q choice slots p).negative =
      (p.positive + p.negative) *
        (slots.map (fun slot => (Cycle.choiceCoefficient N Q (choice slot)).natAbs)).prod := by
  induction slots generalizing p with
  | nil => simp [coefficientPairFold]
  | cons slot slots ih =>
    simp only [coefficientPairFold, List.foldl_cons]
    rw [← coefficientPairFold, ih, CoefficientPair.step_mass]
    simp [mul_assoc]

/-- `prop:time`, paper/paper.tex: the exact
uncancelled coefficient-pair mass is bounded by ell bits per processed
slot, ensuring ordinary arithmetic throughout all eight coordinates. -/
theorem coefficientPairFold_mass_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (slots : List (Fin 8)) :
    let p := coefficientPairFold request.parameters.N request.parameters.Q choice slots ⟨1, 0⟩
    p.positive + p.negative ≤ 2 ^ (request.parameters.ell * slots.length) := by
  dsimp only
  rw [coefficientPairFold_mass]
  simp only [Nat.add_zero, Nat.one_mul]
  induction slots with
  | nil => simp
  | cons slot slots ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.mul_add, Nat.mul_one,
      pow_add]
    exact Nat.mul_le_mul (choiceCoefficient_abs_le request (choice slot)) ih |>.trans_eq (by ring)

end NearQuarticWires.StageGamma
