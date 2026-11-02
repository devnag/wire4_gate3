import Proof.Quartic.Builder.Bounds

/-!
# The mathematical half of the counter of `thm:counter`

Paper: `thm:counter` (Theorem 4.1), paper/paper.tex, items (i) and (ii); its proof.

`CounterMath4 B1 B2` carries a value function on (call, witness word) with the two mathematical properties of
`Transfer.Counter4`: soundness for every call and every witness (the exact type of `Counter4.sound`) and completeness
under the one cap `W ≤ a β 𝒜₄(n)` with polynomial witness length (the exact type of `Counter4.complete`). The machine
of `prop:time` computes the same value function.

`counterMath4_of_paragraphs` builds it from `Builder.value`, the counting algorithm on the cell call of `Builder.cellCall`, with
parameters from the exact rules `Cells.prepare`. Soundness is proved outright (`value_sound`). Completeness takes two
hypotheses, both stated in the paper's quantities:
* `QuarticCap B1 B2`: `lem:asymptotics` and the cap verification of the proof of `thm:counter`;
* `ParagraphBounds witnessLength`: the two paragraph bounds of the proof of `prop:complete`.

`counterMath4_of_random` replaces `ParagraphBounds` by its random part (`RandomBounds`): the deterministic parts of
the two paragraphs are proved (`maskedMass_le_events`, `uncertifiedFraction_le_events`, `cellCall_certified`,
`structuralMass_le`, `populationMass_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open NearCubicGates.Close.Interfaces

/-- **The mathematical half of `Transfer.Counter4`** (`thm:counter`(i),(ii), paper/paper.tex): a value
function `(p̂, κ̂)` on (call, witness word) that is sound for every call and every witness, and complete under the cap
`W ≤ a β 𝒜₄(n)` for large `n` with witnesses of polynomial length. -/
structure CounterMath4 (B1 B2 : ℕ) where
  /-- The interval `(p̂, κ̂)` returned on (call, witness word). -/
  value : Call → List Bool → ℚ × ℚ
  /-- `thm:counter`(i). -/
  sound : ∀ (c : Call) (w : List Bool), |(value c w).1 - c.prob| ≤ (value c w).2
  witnessLength : ℕ → ℕ
  witnessPoly : ∃ C k : ℕ, ∀ n, witnessLength n ≤ C * (n + 1) ^ k
  /-- `thm:counter`(ii). -/
  complete : ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Transfer.Admitted4 B1 B2 c →
    (Transfer.callWires c : ℝ) ≤ a * (c.radius : ℝ) * Transfer.A4 c.n →
    ∃ w : List Bool, w.length ≤ witnessLength c.n ∧ (value c w).2 ≤ c.radius

/-- **`thm:counter`(i),(ii) for the counting algorithm** `Builder.value`, given the cap of `lem:asymptotics` and the
probabilistic part of `prop:complete`. -/
noncomputable def counterMath4_of_paragraphs {B1 B2 : ℕ} (hcap : QuarticCap B1 B2)
    (hlaw : ParagraphBounds witnessLength) :
    CounterMath4 B1 B2 where
  value := value
  sound := value_sound
  witnessLength := witnessLength
  witnessPoly := witnessLength_poly
  complete := value_complete hcap hlaw

/-- The value function of `counterMath4_of_paragraphs` is the counting algorithm `Builder.value`. -/
theorem counterMath4_of_paragraphs_value {B1 B2 : ℕ} (hcap : QuarticCap B1 B2)
    (hlaw : ParagraphBounds witnessLength) :
    (counterMath4_of_paragraphs hcap hlaw).value = value := rfl

/-- **`thm:counter`(i),(ii) for `Builder.value`, with the deterministic parts of `prop:complete` proved**: the
hypotheses are the cap of `lem:asymptotics` and, for every call meeting the hypotheses of `prop:complete`, a witness
law with the three random bounds of its proof (`lem:filter`(a), (c), and (b) with `lem:localize`). -/
noncomputable def counterMath4_of_random {B1 B2 : ℕ} (hcap : QuarticCap B1 B2)
    (hR : ∀ (c : Call) (p : Cells.Parameters) (hs : Cells.ParameterRules (callInput c) p), Shaped c →
      CompletenessConditions c p → Nonempty (RandomBounds c hs (witnessLength c.n))) :
    CounterMath4 B1 B2 :=
  counterMath4_of_paragraphs hcap (paragraphBounds_of_random witnessLength hR)

end NearQuarticWires.Builder
