import Proof.Quartic.Program.Output
import Proof.Quartic.Cells.ParametersScaledFast

/-!
# The counter of `thm:counter` from its mathematical half and the stages of the program

Paper: `thm:counter` (Theorem 4.1), paper/paper.tex; `sec:algorithm`;
`prop:time`; the proof of `thm:counter`.

`counter4_of_components` builds a `Transfer.Counter4` from
* `Builder.CounterMath4` (soundness for every witness and completeness under the cap `W ≤ a β 𝒜₄(n)`) for the
  counting algorithm `Builder.value`, and
* `MachineComponents`, the five stages of the program with their exact outputs and cost ledgers.

The value of the counter is `admittedValue`: the counting algorithm on normalized calls, the sound default
elsewhere. The program is the composition `prep ⨾ cert ⨾ greedy ⨾ main ⨾ output` by `WordFunction.pipe`, so it
computes the value by construction (`counterProgram`). The bound `budget · n^{μ_n} ≤ 2^n` is
`Cells.fast_of_scaled_parameter_ledger` applied to the composed ledger (`total_ledger`): polynomial in the call word,
which is polynomial in `n` for normalized calls (`callWord_length_le`), plus a constant times the three-term envelope
of `prop:time`. Calls that are not normalized are never dispatched, so their cost is polynomial in the call word
(`rest`). The output facts `den`, `dyadic`, `out` are `Program.Output`.

`counterExists4_of_components` is `CounterExists4` from the two halves for every `B₁, B₂ > 0`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearCubicWires.SourceInterfaces NearCubicWires.PolynomialSchedule

variable {B1 B2 : ℕ}

/-! ## The composed program -/

/-- The cost of the composed program: the cost of `WordFunction.pipe`, four times. -/
def totalBudget (K : MachineComponents B1 B2) (c : Call) (w : List Bool) : ℕ :=
  4 * (4 * (4 * (4 * K.prepBudget c w + 4 * K.certBudget c w + 12) + 4 * K.greedyBudget c w + 12) +
    4 * K.mainBudget c w + 12) + 4 * K.outputBudget c w + 12

/-- **The counter program** (`sec:algorithm`): parameter preparation and Steps 1–5, composed. It
maps (call, witness word) to `outputWord (admittedValue … Builder.value c w)`. -/
noncomputable def counterProgram (K : MachineComponents B1 B2) :
    WordFunction (Call × List Bool) requestWord
      (fun r => outputWord (admittedValue B1 B2 Builder.value r.1 r.2)) (fun r => totalBudget K r.1 r.2) :=
  WordFunction.pipe (WordFunction.pipe (WordFunction.pipe (WordFunction.pipe K.prep K.cert) K.greedy) K.main)
    K.output

/-! ## The composed ledger -/

theorem runEnvelope_mono {e e' : ℕ} (h : e ≤ e') (c : Call) :
    runEnvelope B1 B2 e c ≤ runEnvelope B1 B2 e' c := by
  unfold runEnvelope
  split
  · rename_i p hp
    have hn : 0 < c.n := by
      have := (dispatch_admitted hp).1.1
      omega
    exact Cells.ParameterArithmetic.time_envelope_mono _ _ _ _ _ _ _ hn h
  · exact le_rfl

/-- On a normalized call with `W ≠ 0` and selected parameters `p`, the envelope of the ledger is the three-term
envelope of `prop:time` at `p`. -/
theorem runEnvelope_of_prepare {e : ℕ} {c : Call} {p : Cells.Parameters} (hadm : Transfer.Admitted4 B1 B2 c)
    (hW : Transfer.callWires c ≠ 0) (hp : Cells.prepare (Builder.callInput c) = some p) :
    runEnvelope B1 B2 e c = Machine.propTimeEnvelope c.n p.k p.Q p.Jmax p.lambda e := by
  classical
  have hd : dispatch B1 B2 c = some ⟨p, hp⟩ := by
    unfold dispatch
    rw [if_pos ⟨hadm, hW⟩]
    split
    · rename_i p' h'
      rw [hp] at h'
      cases h'
      rfl
    · rename_i h'
      rw [hp] at h'
      cases h'
  unfold runEnvelope
  rw [hd]

/-- On a call with `W = 0`, the envelope of the ledger is `0`. -/
theorem runEnvelope_of_zero {e : ℕ} {c : Call} (hW : Transfer.callWires c = 0) : runEnvelope B1 B2 e c = 0 := by
  classical
  unfold runEnvelope dispatch
  rw [if_neg (fun h => h.2 hW)]

/-- One stage ledger at a larger constant and exponent. -/
theorem LedgerCost.raise {b : Call → List Bool → ℕ} {K e K' e' : ℕ} (hK : K ≤ K') (he : e ≤ e')
    (h : ∀ c w, b c w ≤ K * ((callWord c).length + 1) ^ e + K * runEnvelope B1 B2 e c) (c : Call) (w : List Bool) :
    b c w ≤ K' * ((callWord c).length + 1) ^ e' + K' * runEnvelope B1 B2 e' c := by
  have h1 : ((callWord c).length + 1) ^ e ≤ ((callWord c).length + 1) ^ e' := Nat.pow_le_pow_right (by omega) he
  have h2 := runEnvelope_mono (B1 := B1) (B2 := B2) he c
  calc b c w ≤ K * ((callWord c).length + 1) ^ e + K * runEnvelope B1 B2 e c := h c w
    _ ≤ K' * ((callWord c).length + 1) ^ e' + K' * runEnvelope B1 B2 e' c :=
      Nat.add_le_add (Nat.mul_le_mul hK h1) (Nat.mul_le_mul hK h2)

/-- **The composed ledger** (`prop:time`): the cost of the counter program is polynomial in the
call word plus a constant times the three-term envelope on dispatched calls. -/
theorem total_ledger (K : MachineComponents B1 B2) : ∃ A E : ℕ, ∀ (c : Call) (w : List Bool),
    totalBudget K c w ≤ A * ((callWord c).length + 1) ^ E + A * runEnvelope B1 B2 E c := by
  obtain ⟨Kp, ep, hp⟩ := K.prepCost
  obtain ⟨Kc, ec, hc⟩ := K.certCost
  obtain ⟨Kg, eg, hg⟩ := K.greedyCost
  obtain ⟨Km, em, hm⟩ := K.mainCost
  obtain ⟨Ko, eo, ho⟩ := K.outputCost
  set S := Kp + Kc + Kg + Km + Ko with hS
  set E := ep + ec + eg + em + eo with hE
  refine ⟨1024 * S + 1024, E, fun c w => ?_⟩
  set X := ((callWord c).length + 1) ^ E with hX
  set R := runEnvelope B1 B2 E c with hR
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have bp : K.prepBudget c w ≤ S * X + S * R := by
    have h1 : ((callWord c).length + 1) ^ ep ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 := hp c w
    have h3 : Kp ≤ S := by omega
    calc K.prepBudget c w ≤ Kp * ((callWord c).length + 1) ^ ep := h2
      _ ≤ S * X := Nat.mul_le_mul h3 h1
      _ ≤ S * X + S * R := Nat.le_add_right _ _
  have bc := LedgerCost.raise (show Kc ≤ S by omega) (show ec ≤ E by omega) hc c w
  have bg := LedgerCost.raise (show Kg ≤ S by omega) (show eg ≤ E by omega) hg c w
  have bm := LedgerCost.raise (show Km ≤ S by omega) (show em ≤ E by omega) hm c w
  have bo : K.outputBudget c w ≤ S * X + S * R := by
    have h1 : ((callWord c).length + 1) ^ eo ≤ X := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : Ko ≤ S := by omega
    calc K.outputBudget c w ≤ Ko * ((callWord c).length + 1) ^ eo := ho c w
      _ ≤ S * X := Nat.mul_le_mul h3 h1
      _ ≤ S * X + S * R := Nat.le_add_right _ _
  rw [← hX, ← hR] at bc bg bm
  have hsum : totalBudget K c w ≤ 1024 * (S * X + S * R) + 1024 := by
    unfold totalBudget
    omega
  have hSX : 1024 * (S * X + S * R) + 1024 ≤ (1024 * S + 1024) * X + (1024 * S + 1024) * R := by
    nlinarith
  exact hsum.trans hSX

/-- The polynomial part of the ledger is polynomial in `n` on normalized calls. -/
theorem callWord_pow_le (E : ℕ) : ∃ C d : ℕ, ∀ c : Call, Transfer.Admitted4 B1 B2 c →
    ((callWord c).length + 1) ^ E ≤ C * (c.n + 1) ^ d := by
  have hpoly : PolynomiallyBounded (fun n => (NearCubicGates.Close.CounterAsm.callBound B2 n + 1) ^ E) :=
    polynomiallyBounded_pow (polynomiallyBounded_add (NearCubicGates.Close.CounterAsm.callBound_poly B2)
      (polynomiallyBounded_constant 1)) E
  obtain ⟨C, d, -, hC⟩ := hpoly
  refine ⟨C, d, fun c hadm => ?_⟩
  have h1 := callWord_length_le hadm
  exact (Nat.pow_le_pow_left (by omega) E).trans (hC c.n)

/-! ## `thm:counter` -/

/-- **The counter of `thm:counter`** (Theorem 4.1, paper/paper.tex) at fixed `B₁, B₂`, from the
mathematical half `M` (whose value is the counting algorithm) and the five stages `K` of the program. -/
noncomputable def counter4_of_components (M : Builder.CounterMath4 B1 B2) (hM : M.value = Builder.value)
    (K : MachineComponents B1 B2) : Transfer.Counter4 B1 B2 where
  value := admittedValue B1 B2 Builder.value
  budget := totalBudget K
  program := counterProgram K
  dyadic := admittedValue_dyadic B1 B2
  sound := by
    intro c w
    by_cases h : Transfer.Admitted4 B1 B2 c
    · rw [admittedValue_of_admitted _ h, ← hM]
      exact M.sound c w
    · rw [admittedValue_of_not_admitted _ h]
      exact Builder.soundDefault_sound c
  witnessLength := M.witnessLength
  witnessPoly := M.witnessPoly
  complete := by
    obtain ⟨a, ha, onset, h⟩ := M.complete
    refine ⟨a, ha, onset, fun c hn hadm hcap => ?_⟩
    obtain ⟨w, hw, hr⟩ := h c hn hadm hcap
    refine ⟨w, hw, ?_⟩
    rw [admittedValue_of_admitted _ hadm, ← hM]
    exact hr
  fast := by
    obtain ⟨A, E, hA⟩ := total_ledger K
    obtain ⟨C, d, hC⟩ := callWord_pow_le (B1 := B1) (B2 := B2) E
    apply Cells.fast_of_scaled_parameter_ledger B1 B2 (totalBudget K)
    · refine ⟨A * C * 2 ^ d + A, E, d, 1, fun c p hn hadm hW hp w => ?_⟩
      have h1 := hA c w
      rw [runEnvelope_of_prepare hadm hW hp] at h1
      have h2 := hC c hadm
      have h3 : (c.n + 1) ^ d ≤ 2 ^ d * c.n ^ d := by
        rw [← mul_pow]
        exact Nat.pow_le_pow_left (by omega) d
      generalize Machine.propTimeEnvelope c.n p.k p.Q p.Jmax p.lambda E = V at h1 ⊢
      generalize ((callWord c).length + 1) ^ E = X at h1 h2
      generalize c.n ^ d = Y at h3 ⊢
      generalize (c.n + 1) ^ d = Z at h2 h3
      generalize 2 ^ d = P at h3 ⊢
      have h4 : X ≤ C * (P * Y) := h2.trans (Nat.mul_le_mul_left _ h3)
      have e : (A * C * P + A) * (V + Y) = A * (C * (P * Y)) + A * V + (A * C * P * V + A * Y) := by ring
      calc totalBudget K c w ≤ A * X + A * V := h1
        _ ≤ A * (C * (P * Y)) + A * V := Nat.add_le_add_right (Nat.mul_le_mul_left _ h4) _
        _ ≤ (A * C * P + A) * (V + Y) := by rw [e]; exact Nat.le_add_right _ _
    · refine ⟨A * C, d, 0, fun c _ hadm hW w => ?_⟩
      have h1 := hA c w
      rw [runEnvelope_of_zero hW] at h1
      have h2 := hC c hadm
      calc totalBudget K c w ≤ A * ((callWord c).length + 1) ^ E + A * 0 := h1
        _ ≤ A * (C * (c.n + 1) ^ d) := by rw [mul_zero, add_zero]; exact Nat.mul_le_mul_left _ h2
        _ = A * C * (c.n + 1) ^ d := by ring
  rest := by
    obtain ⟨A, E, hA⟩ := total_ledger K
    refine ⟨A, E, fun c w hna => ?_⟩
    have h1 := hA c w
    rw [runEnvelope_of_not_admitted hna, mul_zero, add_zero] at h1
    exact h1
  den := admittedValue_den B1 B2
  out := ⟨50, 1, fun c w => by
    have := admittedValue_outputWord_length B1 B2 c w
    rw [pow_one]
    omega⟩

/-- The value of the constructed counter is the counting algorithm on every normalized call. -/
theorem counter4_of_components_value (M : Builder.CounterMath4 B1 B2) (hM : M.value = Builder.value)
    (K : MachineComponents B1 B2) {c : Call} (h : Transfer.Admitted4 B1 B2 c) (w : List Bool) :
    (counter4_of_components M hM K).value c w = Builder.value c w :=
  admittedValue_of_admitted _ h w

/-- **`thm:counter` from its two halves** (paper/paper.tex): if, for every `B₁, B₂ > 0`, the counting
algorithm `Builder.value` has the mathematical properties `Builder.CounterMath4` and the five stages of its program
exist (`MachineComponents`), then `CounterExists4`. -/
theorem counterExists4_of_components
    (hmath : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → ∃ M : Builder.CounterMath4 B1 B2, M.value = Builder.value)
    (hmachine : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (MachineComponents B1 B2)) :
    Transfer.CounterExists4 := by
  intro B1 B2 h1 h2
  obtain ⟨M, hM⟩ := hmath B1 B2 h1 h2
  obtain ⟨K⟩ := hmachine B1 B2 h1 h2
  exact ⟨counter4_of_components M hM K⟩

end NearQuarticWires.Program
