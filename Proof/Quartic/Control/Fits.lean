import Proof.Quartic.Control.Seed

/-!
# The register capacity for reading the number of rounds

Paper: `sec:params`, paper/paper.tex (the parameters are written as numbers), and Step 3. The registers of the word programs are unary counters of a fixed capacity; reading the call word and `S`
needs the capacity to exceed every number and every list length met (`ReadFits`). Every such number is written in
the word itself, so a capacity exponential in the length of the word is enough (`readFits_of_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord gateWord bitWord circuitWord NCircuit Call callWord kindTag)

local notation "intWord" => NearCubicGates.Close.Interfaces.intWord

theorem natBitLength_le_natWord (x : ℕ) : natBitLength x + 1 ≤ (natWord x).length := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; omega

theorem natBitLength_le_intWord (z : ℤ) : natBitLength z.natAbs + 2 ≤ (intWord z).length := by
  rw [intWord_length]; omega

theorem length_le_flatMap {α : Type} (g : α → List Bool) (xs : List α) (x : α) (hx : x ∈ xs) :
    (g x).length ≤ (xs.flatMap g).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem count_le_flatMap {α : Type} (g : α → List Bool) (xs : List α) (hg : ∀ x, 1 ≤ (g x).length) :
    xs.length ≤ (xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons]; have := hg x; omega

theorem listWord_count {α : Type} (g : α → List Bool) (xs : List α) (hg : ∀ x, 1 ≤ (g x).length) :
    natBitLength xs.length + 1 ≤ (listWord g xs).length ∧ xs.length ≤ (listWord g xs).length := by
  have h1 := natBitLength_le_natWord xs.length
  have h2 := count_le_flatMap g xs hg
  unfold listWord; simp only [List.length_append]; omega

theorem listWord_elem {α : Type} (g : α → List Bool) (xs : List α) (x : α) (hx : x ∈ xs) :
    (g x).length ≤ (listWord g xs).length := by
  have := length_le_flatMap g xs x hx
  unfold listWord; simp only [List.length_append]; omega

theorem intWord_pos (z : ℤ) : 1 ≤ (intWord z).length := by rw [intWord_length]; omega

theorem natWord_pos (x : ℕ) : 1 ≤ (natWord x).length := by have := natBitLength_le_natWord x; omega

theorem gateWord_pos {n : ℕ} (g : NormalizedThresholdGate n) : 1 ≤ (gateWord g).length := by
  unfold gateWord; have := intWord_pos g.threshold; simp only [List.length_append]; omega

theorem bitWord_pos (b : Bool) : 1 ≤ (bitWord b).length := by unfold bitWord; exact natWord_pos _

theorem pow_le_of_le {a b cap : ℕ} (h : a ≤ b) (hc : 2 ^ b ≤ cap) : 2 ^ a ≤ cap :=
  le_trans (Nat.pow_le_pow_right (by norm_num) h) hc

theorem le_of_pow {a cap : ℕ} (hc : 2 ^ a ≤ cap) : a ≤ cap := le_trans (Nat.lt_two_pow_self).le hc

/-- A circuit fits a capacity exponential in the length of its word. -/
theorem circuitFits_of_le {n : ℕ} (C : NCircuit n) (cap : ℕ) (hc : 2 ^ ((circuitWord C).length + 2) ≤ cap) :
    NearCubicGates.Close.Codec.CircuitFits cap C := by
  have hL := le_of_pow hc
  have hcw : ∀ u v w : List Bool, circuitWord C = u ++ v ++ w → v.length ≤ (circuitWord C).length := by
    intro u v w h; rw [h]; simp only [List.length_append]; omega
  have hG := listWord_count gateWord C.gates gateWord_pos
  have hGc : (listWord gateWord C.gates).length ≤ (circuitWord C).length :=
    hcw [] _ (listWord intWord C.coeffs ++ listWord bitWord C.table) (by unfold circuitWord; simp [List.append_assoc])
  have hK := listWord_count intWord C.coeffs intWord_pos
  have hKc : (listWord intWord C.coeffs).length ≤ (circuitWord C).length :=
    hcw (listWord gateWord C.gates) _ (listWord bitWord C.table) (by unfold circuitWord; simp [List.append_assoc])
  have hT := listWord_count bitWord C.table bitWord_pos
  have hTc : (listWord bitWord C.table).length ≤ (circuitWord C).length :=
    hcw (listWord gateWord C.gates ++ listWord intWord C.coeffs) _ [] (by unfold circuitWord; simp)
  refine ⟨fun gt hgt => ?_, pow_le_of_le (by omega) hc, by omega, pow_le_of_le (by omega) hc, by omega,
    fun z hz => ?_, pow_le_of_le (by omega) hc, by omega, ?_⟩
  · have hgw := listWord_elem gateWord C.gates gt hgt
    have hW := listWord_count intWord (List.ofFn gt.weight) intWord_pos
    have hWg : (listWord intWord (List.ofFn gt.weight)).length ≤ (gateWord gt).length := by
      unfold gateWord; simp only [List.length_append]; omega
    have hlen : (List.ofFn gt.weight).length = n := List.length_ofFn
    have hW1 : natBitLength n + 1 ≤ (listWord intWord (List.ofFn gt.weight)).length := by
      have := hW.1; rwa [hlen] at this
    have hW2 : n ≤ (listWord intWord (List.ofFn gt.weight)).length := by
      have := hW.2; rwa [hlen] at this
    refine ⟨pow_le_of_le (by omega) hc, by omega, fun z hz => ?_, ?_⟩
    · have := listWord_elem intWord (List.ofFn gt.weight) z hz
      have := natBitLength_le_intWord z; omega
    · have := natBitLength_le_intWord gt.threshold
      have : (intWord gt.threshold).length ≤ (gateWord gt).length := by
        unfold gateWord; simp only [List.length_append]; omega
      omega
  · have := listWord_elem intWord C.coeffs z hz
    have := natBitLength_le_intWord z; omega
  · have := Nat.one_le_two_pow (n := (circuitWord C).length + 1)
    have : 2 ≤ 2 ^ ((circuitWord C).length + 2) := by
      rw [pow_succ]; omega
    omega


/-- **The capacity for reading `S`**: a capacity of `2^(ℓ + 2)`, `ℓ` the length of the call word, the nineteen
numbers and `natWord S`, holds every number and list length read. -/
theorem readFits_of_le (c : Call) (xs : List ℕ) (S cap : ℕ)
    (hc : 2 ^ ((callWord c).length + (xs.flatMap natWord).length + (natWord S).length + 2) ≤ cap) :
    ReadFits cap c xs S := by
  have hL := le_of_pow hc
  have hcl := congrArg List.length (callWord_split c)
  simp only [List.length_append] at hcl
  have hn := natBitLength_le_natWord c.n
  have hk := natBitLength_le_natWord (kindTag c.kind)
  have hP := listWord_count natWord c.parity natWord_pos
  have hnum := natBitLength_le_intWord c.radius.num
  have hden := natBitLength_le_natWord c.radius.den
  have hS := natBitLength_le_natWord S
  refine ⟨by omega, by omega, circuitFits_of_le c.first cap (pow_le_of_le (by omega) hc),
    circuitFits_of_le c.second cap (pow_le_of_le (by omega) hc), pow_le_of_le (by omega) hc, by omega,
    fun x hx => ?_, by omega, by omega, fun x hx => ?_, pow_le_of_le (by omega) hc⟩
  · have := listWord_elem natWord c.parity x hx
    have := natBitLength_le_natWord x; omega
  · have := length_le_flatMap natWord xs x hx
    have := natBitLength_le_natWord x; omega

end NearQuarticWires.Control
