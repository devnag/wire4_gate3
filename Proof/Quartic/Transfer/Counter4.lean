import Proof.Gates.Interfaces.Counter

/-!
# The counter interface of the wire-4 proof: `Counter4`, `CounterExists4`

Paper: `paper/paper.tex`, §3.1 "Normalized calls and the counting theorem" and `thm:counter`
(Theorem 4.1). This is the base's `Counter B1 B2` (`Proof/Gates/Interfaces/Counter.lean`, the interface of
[NagCG, Theorem 3.1]) with the two changes the paper states at `thm:counter`:
* the size of a call is the **wire count** `W = W(C¹) + W(C²)` of its circuits (`def:class`:
  `W(C) = G + Σ_i f_i`, `f_i` = number of nonzero weights of occurrence `i`);
* completeness has **one cap** `W ≤ a·β·𝒜₄(n)` for all three call kinds, `𝒜₄(n) = n⁴ / (λ_n^{17/4} μ_n^{15/2})`.

**Circuit representation.** A `SYM∘THR` circuit with integer weights and an explicit lookup table is the base's
`NCircuit` with every top coefficient equal to `1` (`UnitTop`): its score is then the number `Σ_i T_i` of true
occurrences, and the table (index `score + G`, length `2G + 1`) holds the lookup `g` on `[0, G]` at indices `G … 2G`.
Reusing `NCircuit` keeps the base's `Call`, `callWord`, `outputWord` and `WordFunction` program type, which is what the
weak machine's guess format, call builder and term loop consume (`Proof/Gates/Worker/{Meaning, Calls, Format}`): the
worker guesses `NCircuit`s and builds `Call`s from them, so the transfer needs no new circuit codec.
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- The fan-in `f` of a normalized gate: the number of inputs with a nonzero weight (`def:class`). -/
def fanIn {n : ℕ} (g : NormalizedThresholdGate n) : ℕ :=
  (Finset.univ.filter fun i : Fin n => g.weight i ≠ 0).card

/-- The wire count `W(C) = G + Σ_i f_i` of a normalized circuit: one top wire per occurrence plus its fan-in
(`def:class`). -/
def wires {n : ℕ} (C : NCircuit n) : ℕ := (C.gates.map fun g => fanIn g + 1).sum

/-- Every top coefficient is `1`: the circuit is a `SYM∘THR` circuit whose score is its count of true occurrences. -/
def UnitTop {n : ℕ} (C : NCircuit n) : Prop := ∀ a ∈ C.coeffs, a = 1

/-- The total wire count `W = W(C¹) + W(C²)` of a call (`sec:counting`; `W(C²) = 0` for single and parity calls, whose
second circuit is empty). -/
def callWires (c : Call) : ℕ := wires c.first + wires c.second

/-- The normalized calls of §3.1 (`sec:counting`) at parameters `B₁, B₂`: `n ≥ 4`; `SYM∘THR` circuits on `n` inputs
with integer weights and thresholds below `2^{B₀}` and explicit tables; total wire count `W ≤ 2n⁴`; a rational radius
`n^{-B₁} ≤ β ≤ 1/16` encoded in at most `n^{B₂}` bits. -/
def Admitted4 (B1 B2 : ℕ) (c : Call) : Prop :=
  4 ≤ c.n ∧ c.first.WellFormed (Call.B0 c.n) ∧ c.second.WellFormed (Call.B0 c.n) ∧
    UnitTop c.first ∧ UnitTop c.second ∧
    (c.kind ≠ .pair → c.second = NCircuit.empty c.n) ∧
    (c.kind ≠ .parity → c.parity = []) ∧ (∀ i ∈ c.parity, i < c.n) ∧
    callWires c ≤ 2 * c.n ^ 4 ∧
    1 ≤ c.radius * (c.n : ℚ) ^ B1 ∧ c.radius ≤ 1 / 16 ∧ (ratWord c.radius).length ≤ c.n ^ B2 ∧
    c.parity.length ≤ c.n

/-- `𝒜₄(n) = n⁴ / (λ_n^{17/4} μ_n^{15/2})` (`thm:main`), with `λ_n = ⌈lg n⌉`, `μ_n = ⌈lg λ_n⌉`. -/
noncomputable def A4 (n : ℕ) : ℝ :=
  (n : ℝ) ^ 4 / (((NearCubicGates.Target.lambda n : ℕ) : ℝ) ^ ((17 : ℝ) / 4) *
    ((NearCubicGates.Target.mu n : ℕ) : ℝ) ^ ((15 : ℝ) / 2))

/-- **The counter of `thm:counter`** (Theorem 4.1) at fixed `B₁, B₂`: one deterministic program on
(normalized call, witness word) with
* (i) soundness for every witness, with dyadic outputs whose denominators divide `2^{n+1}` (`den`);
* (ii) completeness under the one cap `W ≤ a·β·𝒜₄(n)` for all three call kinds, with a witness of polynomial length;
* (iii) time `2^n / n^{μ_n}` on every normalized call (`fast`), and polynomial time in the call word on every other
  call (`rest`), with outputs of polynomial length (`out`).
`den`, `out` and `rest` are what the weak machine consumes (the base's `Counter.DenOK`, `Counter.OutOK`,
`Counter.rest`); they are fields so that one object yields the counter and every property the transfer uses. -/
structure Counter4 (B1 B2 : ℕ) where
  /-- The interval `(p̂, κ̂)` the program prints on (call, witness word). -/
  value : Call → List Bool → ℚ × ℚ
  budget : Call → List Bool → ℕ
  program : WordFunction (Call × List Bool) (fun r => frame (callWord r.1) ++ frame r.2)
    (fun r => outputWord (value r.1 r.2)) (fun r => budget r.1 r.2)
  dyadic : ∀ c w, IsDyadic (value c w).1 ∧ IsDyadic (value c w).2
  /-- `thm:counter` (i). -/
  sound : ∀ (c : Call) (w : List Bool), |(value c w).1 - c.prob| ≤ (value c w).2
  witnessLength : ℕ → ℕ
  witnessPoly : ∃ C k : ℕ, ∀ n, witnessLength n ≤ C * (n + 1) ^ k
  /-- `thm:counter` (ii): one cap `W ≤ a β 𝒜₄(n)` on the total wire count, for single, pair and parity calls. -/
  complete : ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Admitted4 B1 B2 c →
    (callWires c : ℝ) ≤ a * (c.radius : ℝ) * A4 c.n →
    ∃ w : List Bool, w.length ≤ witnessLength c.n ∧ (value c w).2 ≤ c.radius
  /-- `thm:counter` (iii): `2^n / n^{μ_n}` steps on every normalized call. -/
  fast : ∃ onset : ℕ, ∀ c : Call, onset ≤ c.n → Admitted4 B1 B2 c → ∀ w : List Bool,
    budget c w * c.n ^ NearCubicGates.Target.mu c.n ≤ 2 ^ c.n
  /-- Calls that are not normalized are answered in time polynomial in the call word, whatever the witness. -/
  rest : ∃ K e : ℕ, ∀ (c : Call) (w : List Bool), ¬ Admitted4 B1 B2 c →
    budget c w ≤ K * ((callWord c).length + 1) ^ e
  /-- Dyadic with denominator dividing `2^{n+1}` (the base's `Counter.DenOK`). -/
  den : ∀ (c : Call) (w : List Bool),
    ((value c w).1 * 2 ^ (c.n + 1)).den = 1 ∧ ((value c w).2 * 2 ^ (c.n + 1)).den = 1
  /-- Output words of polynomial length (the base's `Counter.OutOK`). -/
  out : ∃ C e : ℕ, ∀ (c : Call) (w : List Bool), (outputWord (value c w)).length ≤ C * (c.n + 1) ^ e

/-- `thm:counter` for every pair of positive integers `B₁, B₂`. -/
def CounterExists4 : Prop := ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (Counter4 B1 B2)

end NearQuarticWires.Transfer
