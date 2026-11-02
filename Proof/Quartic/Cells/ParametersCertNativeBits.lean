import Proof.Quartic.Cells.ParametersCertWeights

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open ParameterArithmetic

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: one fixed polynomial width for signed
coefficients of the actual pre-certification formulas. -/
def nativeCertificateBits (B1 n : ℕ) : ℕ :=
  100 * (preparationCoefficient B1 + 1) ^ 2 * (n + 1) ^ (2 * (B1 + 12)) + 2

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual expansion coefficient with the formal
mass envelope fits the fixed polynomial native width. -/
theorem actual_coefficient_native_width {V : ℕ} (F : Formula V) (B1 n : ℕ)
    (hmass : F.mass ≤ 2 ^ certificateBitEnvelope (preparationEnvelope B1 n))
    (term : Finset (Fin V) × ℤ)
    (ht : term ∈ NearCubicGates.Close.Expand.expansionMachine.expand ⟨V, F⟩) :
    term.2.natAbs < 2 ^ nativeCertificateBits B1 n ∧
      Nat.size term.2.natAbs ≤ nativeCertificateBits B1 n := by
  have h := actual_expansion_coefficient_bits F _ hmass term ht
  have hp := certificate_bit_envelope_polynomial B1 n
  have hwidth : certificateBitEnvelope (preparationEnvelope B1 n) + 1 ≤
      nativeCertificateBits B1 n := by unfold nativeCertificateBits; omega
  exact ⟨h.1.trans_le (Nat.pow_le_pow_right (by norm_num) hwidth), h.2.trans hwidth⟩

/-- `eq:testE`, `eq:testPhi` and `lem:print`, paper/paper.tex: the literal moment AST has a
polynomial formal-mass binary height for all proposed coefficients
within their actual selected scales, without a certification premise. -/
theorem call_moment_formal_mass_bound (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4)
    (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1)
    (hf : ∀ t, (f t).natAbs ≤ 1 + c.n + p.M1 + p.A) :
    (StagePrint.callMomentFormula c hs w walk j f sigma).mass ≤
      2 ^ certificateBitEnvelope (preparationEnvelope B1 c.n) := by
  let E := preparationEnvelope B1 c.n
  let G := (Builder.allGates c).length
  let B := 1 + c.n + p.M1 + p.A
  have hscalar := hs.scalar_preparation_bounds B1 hb
  have hG : G ≤ E := by
    simpa only [G, E, Builder.allGates, List.length_append, Builder.callInput] using
      hs.occurrences_preparation_envelope B1
  have hn : c.n ≤ E := (Nat.le_succ c.n).trans (preparation_envelope_arity B1 c.n)
  have hM : p.M1 ≤ E := hscalar.M1
  have hA : p.A ≤ E := hscalar.A
  have hB : B ≤ 2 ^ (E + 2) := by
    have hraw : B ≤ 4 * (E + 1) := by dsimp only [B]; omega
    calc
      B ≤ 4 * (E + 1) := hraw
      _ ≤ 4 * 2 ^ E := Nat.mul_le_mul_left _ Nat.lt_two_pow_self
      _ = _ := by rw [pow_add]; norm_num; ring
  have hsign : ∀ e : Fin 8, (Cycle.signValue (sigma e)).natAbs ≤ 1 := by
    intro e
    cases sigma e <;> decide
  have hwalk : (StagePrint.callWalkFormula c j f sigma).mass ≤ 32 * G * B := by
    exact pooled_walk_formula_mass_le (by norm_num : 0 < 4)
      (StagePrint.circuitWeights c j f) (fun e => Cycle.signValue (sigma e)) B
      (circuit_weights_natAbs_le c j f B hf) hsign
  have hmoment := moment_formula_mass_le
    (fun e => StagePrint.selectedMaskFormula (by norm_num : 0 < 4)
      (Builder.selection c (p := p) w) (StagePrint.callStructural c hs walk e) e p.tau p.Xmax)
    (StagePrint.callWalkFormula c j f sigma) G p.Xmax p.k B
    (fun e => selected_mask_mass_bound (by norm_num : 0 < 4)
      (Builder.selection c (p := p) w) (StagePrint.callStructural c hs walk e) e p.tau p.Xmax)
    hwalk
  exact hmoment.trans (certificate_formal_moment_mass_bound E G p.Xmax p.k B
    hG hscalar.Xmax hscalar.k hB)

/-- `eq:testE` and `lem:print`, paper/paper.tex: every actual proposed digit moment has the uniform
formal mass bound, including bad columns and arbitrary witnesses. -/
theorem call_digit_moment_mass_bound (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (sigma : Cycle.SignPattern 4) (r : Fin (p.J - 1 + 1))
    (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1) :
    (StagePrint.callMomentFormula c hs w walk j (StagePrint.callDigitWeights c hs w j r) sigma).mass ≤
      2 ^ certificateBitEnvelope (preparationEnvelope B1 c.n) := by
  apply call_moment_formal_mass_bound c hs w walk j _ sigma B1 hb
  intro t
  exact (call_digit_weights_natAbs_le c hs w j r t).trans (by omega)

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the complete final-error moment has the same
formal bound before any strict column test. -/
theorem call_final_moment_mass_bound (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (sigma : Cycle.SignPattern 4) (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1) :
    (StagePrint.callMomentFormula c hs w walk j (StagePrint.callFinalWeights c p w j) sigma).mass ≤
      2 ^ certificateBitEnvelope (preparationEnvelope B1 c.n) := by
  apply call_moment_formal_mass_bound c hs w walk j _ sigma B1 hb
  intro t
  exact (call_final_weights_natAbs_le c p w j t).trans (by omega)

/-- `eq:testX` and `lem:print`, paper/paper.tex: the actual selected population moment has the
same formal binary-height envelope, on all atom assignments. -/
theorem call_population_moment_mass_bound (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool) (e : Fin 8)
    (structural : Bool) (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1) :
    (StagePrint.selectedPopulationMomentFormula (by norm_num : 0 < 4)
      (Builder.selection c (p := p) w) e structural p.k).mass ≤
      2 ^ certificateBitEnvelope (preparationEnvelope B1 c.n) := by
  let E := preparationEnvelope B1 c.n
  let G := (Builder.allGates c).length
  have hG : G ≤ E := by
    simpa only [G, E, Builder.allGates, List.length_append, Builder.callInput] using
      hs.occurrences_preparation_envelope B1
  have hk : p.k ≤ E := (hs.scalar_preparation_bounds B1 hb).k
  have hbase : 16 * G ≤ 2 ^ (E + 4) := by
    calc
      _ ≤ 16 * 2 ^ E := Nat.mul_le_mul_left _ (hG.trans Nat.lt_two_pow_self.le)
      _ = _ := by rw [pow_add]; norm_num; ring
  calc
    _ ≤ (16 * G) ^ (2 * p.k) := selected_population_moment_mass_le _ _ _ _ _
    _ ≤ (2 ^ (E + 4)) ^ (2 * p.k) := Nat.pow_le_pow_left hbase _
    _ = 2 ^ ((E + 4) * (2 * p.k)) := (pow_mul _ _ _).symm
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hh := Nat.mul_le_mul_left (E + 4) (Nat.mul_le_mul_left 2 hk)
      unfold certificateBitEnvelope
      nlinarith only [hh, Nat.zero_le E]

/-- `eq:testE` and `prop:time`, paper/paper.tex: actual expanded digit coefficients fit one fixed
polynomial signed native field, without using syntactic weight. -/
theorem call_digit_moment_coefficient_bits (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (sigma : Cycle.SignPattern 4) (r : Fin (p.J - 1 + 1))
    (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1)
    (term : Finset (Fin (17 * (Builder.allGates c).length)) × ℤ)
    (ht : term ∈ NearCubicGates.Close.Expand.expansionMachine.expand
      ⟨_, StagePrint.callMomentFormula c hs w walk j (StagePrint.callDigitWeights c hs w j r) sigma⟩) :
    term.2.natAbs < 2 ^ nativeCertificateBits B1 c.n ∧
      Nat.size term.2.natAbs ≤ nativeCertificateBits B1 c.n :=
  actual_coefficient_native_width _ B1 c.n
    (call_digit_moment_mass_bound c hs w walk j sigma r B1 hb) term ht

/-- `eq:testPhi` and `prop:time`, paper/paper.tex: actual expanded final-error coefficients fit
the same fixed polynomial signed native field on every column. -/
theorem call_final_moment_coefficient_bits (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2) (sigma : Cycle.SignPattern 4)
    (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1)
    (term : Finset (Fin (17 * (Builder.allGates c).length)) × ℤ)
    (ht : term ∈ NearCubicGates.Close.Expand.expansionMachine.expand
      ⟨_, StagePrint.callMomentFormula c hs w walk j (StagePrint.callFinalWeights c p w j) sigma⟩) :
    term.2.natAbs < 2 ^ nativeCertificateBits B1 c.n ∧
      Nat.size term.2.natAbs ≤ nativeCertificateBits B1 c.n :=
  actual_coefficient_native_width _ B1 c.n
    (call_final_moment_mass_bound c hs w walk j sigma B1 hb) term ht

/-- `eq:testX` and `prop:time`, paper/paper.tex: actual expanded population-moment coefficients
fit the common polynomial field before certification. -/
theorem call_population_moment_coefficient_bits (c : Call) {p : Parameters}
    (hs : ParameterRules (Builder.callInput c) p) (w : List Bool) (e : Fin 8)
    (structural : Bool) (B1 : ℕ) (hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1)
    (term : Finset (Fin (17 * (Builder.allGates c).length)) × ℤ)
    (ht : term ∈ NearCubicGates.Close.Expand.expansionMachine.expand
      ⟨_, StagePrint.selectedPopulationMomentFormula (by norm_num : 0 < 4)
        (Builder.selection c (p := p) w) e structural p.k⟩) :
    term.2.natAbs < 2 ^ nativeCertificateBits B1 c.n ∧
      Nat.size term.2.natAbs ≤ nativeCertificateBits B1 c.n :=
  actual_coefficient_native_width _ B1 c.n
    (call_population_moment_mass_bound c hs w e structural B1 hb) term ht

end NearQuarticWires.Cells
