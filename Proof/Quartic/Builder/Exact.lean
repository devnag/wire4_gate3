import Proof.Quartic.Builder.Fourier

/-!
# Exact evaluation of a call with no wires

Paper: `sec:params`, paper/paper.tex: "if `W = 0`, the circuits are constant and the call is
evaluated exactly (a nonempty parity has probability `1/2`)".

A call with `W = 0` has no occurrences, so each circuit is the constant `table[0]` (`eval_of_wires_zero`). A single
call has probability `[t_1]`, a pair call `[t_1 ⊕ t_2]`. For a parity call, the parity `PAR_Σ` of the index list is
the parity of the indices `i < n` occurring an odd number of times (`bitSign_parityOf`); if there is one, flipping
that input bit negates the predicate and the probability is `1/2` (`prob_of_flip`), and otherwise the parity is `0`
and the probability is `[t_1]`. `closedValue_eq` proves that the closed form `closedValue` is `(p_true, 0)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-- The value `0` or `1` of a bit, as a rational number. -/
def bitQ (b : Bool) : ℚ := if b then 1 else 0

/-- The constant value `table[0]` of a circuit with no occurrences. -/
def constantValue {n : ℕ} (C : NCircuit n) : Bool := C.table.getD 0 false

/-- Whether some input index `i < n` occurs an odd number of times in the parity list of the call. -/
def oddParity (c : Call) : Bool := decide (∃ i ∈ Finset.range c.n, c.parity.count i % 2 = 1)

/-- `sec:params`, paper/paper.tex: the exact value `(p_true, 0)` of a call with `W = 0`, in closed
form. -/
def closedValue (c : Call) : ℚ × ℚ :=
  match c.kind with
  | .single => (bitQ (constantValue c.first), 0)
  | .pair => (bitQ (xor (constantValue c.first) (constantValue c.second)), 0)
  | .parity => if oddParity c then (1 / 2, 0) else (bitQ (constantValue c.first), 0)

/-- A circuit with wire count `0` has no occurrences. -/
theorem gates_nil_of_wires_zero {n : ℕ} (C : NCircuit n) (h : Transfer.wires C = 0) : C.gates = [] := by
  unfold Transfer.wires at h
  cases hg : C.gates with
  | nil => rfl
  | cons g l =>
    rw [hg] at h
    simp at h

/-- A circuit with no occurrences and one coefficient per occurrence is the constant `table[0]`. -/
theorem eval_of_gates_nil {n : ℕ} (C : NCircuit n) (hl : C.gates.length = C.coeffs.length) (hg : C.gates = [])
    (z : BitInput n) : C.eval z = constantValue C := by
  have hc : C.coeffs = [] := by
    rw [hg] at hl
    exact List.eq_nil_of_length_eq_zero hl.symm
  unfold NCircuit.eval NCircuit.score NCircuit.topWeight constantValue
  rw [hg, hc]
  rfl

/-- The sign of the call's parity is a product over the distinct indices, each to the power of its multiplicity. -/
theorem bitSign_parityOf (c : Call) (z : BitInput c.n) :
    Sampler.bitSign (c.parityOf z) = ∏ m ∈ c.parity.toFinset,
      Sampler.bitSign (if h : m < c.n then z ⟨m, h⟩ else false) ^ c.parity.count m := by
  unfold Call.parityOf
  simp only [List.foldl_map]
  rw [Sampler.bitSign_foldl, Finset.prod_list_map_count]
  simp [Sampler.bitSign]

theorem bitSign_eq_one_iff (b : Bool) : Sampler.bitSign b = 1 ↔ b = false := by
  cases b <;> norm_num [Sampler.bitSign]

theorem bitSign_pow_even (b : Bool) (k : ℕ) (hk : k % 2 = 0) : Sampler.bitSign b ^ k = 1 := by
  cases b
  · simp [Sampler.bitSign]
  · simp only [Sampler.bitSign, if_true]
    exact Even.neg_one_pow (Nat.even_iff.mpr hk)

/-- With every index of even multiplicity, the parity is `0`. -/
theorem parityOf_eq_false (c : Call) (hodd : oddParity c = false) (z : BitInput c.n) : c.parityOf z = false := by
  rw [← bitSign_eq_one_iff, bitSign_parityOf]
  apply Finset.prod_eq_one
  intro m _
  by_cases hm : m < c.n
  · rw [dif_pos hm]
    apply bitSign_pow_even
    unfold oddParity at hodd
    simp only [decide_eq_false_iff_not, not_exists, not_and] at hodd
    have := hodd m (Finset.mem_range.mpr hm)
    omega
  · rw [dif_neg hm]
    simp [Sampler.bitSign]

/-- Flipping an input bit of odd multiplicity negates the sign of the parity. -/
theorem bitSign_parityOf_flip (c : Call) (i : Fin c.n) (hi : c.parity.count (i : ℕ) % 2 = 1) (z : BitInput c.n) :
    Sampler.bitSign (c.parityOf (Function.update z i (!z i))) = -Sampler.bitSign (c.parityOf z) := by
  rw [bitSign_parityOf, bitSign_parityOf]
  have hmem : (i : ℕ) ∈ c.parity.toFinset := by
    rw [List.mem_toFinset]
    exact List.count_pos_iff.mp (by omega)
  rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
  have hrest : ∏ m ∈ c.parity.toFinset.erase (i : ℕ),
      Sampler.bitSign (if h : m < c.n then Function.update z i (!z i) ⟨m, h⟩ else false) ^ c.parity.count m =
      ∏ m ∈ c.parity.toFinset.erase (i : ℕ),
        Sampler.bitSign (if h : m < c.n then z ⟨m, h⟩ else false) ^ c.parity.count m := by
    refine Finset.prod_congr rfl fun m hm => ?_
    have hne : m ≠ (i : ℕ) := (Finset.mem_erase.mp hm).1
    by_cases h : m < c.n
    · rw [dif_pos h, dif_pos h, Function.update_of_ne (fun e => hne (congrArg Fin.val e))]
    · rw [dif_neg h, dif_neg h]
  rw [hrest, dif_pos i.isLt, dif_pos i.isLt]
  simp only [Fin.eta, Function.update_self]
  have hodd : Odd (c.parity.count (i : ℕ)) := Nat.odd_iff.mpr hi
  cases z i
  · simp only [Bool.not_false, Sampler.bitSign, if_true, Bool.false_eq_true, if_false, one_pow,
      hodd.neg_one_pow]
    ring
  · simp only [Bool.not_true, Sampler.bitSign, if_true, Bool.false_eq_true, if_false, one_pow,
      hodd.neg_one_pow]
    ring

/-- The probability as an average of bits. -/
theorem prob_eq_sum (c : Call) : c.prob = (∑ z : BitInput c.n, bitQ (c.predicate z)) / 2 ^ c.n := by
  unfold Call.prob
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold bitQ
  split_ifs <;> simp_all

theorem card_cube (n : ℕ) : (Fintype.card (BitInput n) : ℚ) = 2 ^ n := by
  simp [BitInput]

/-- A constant predicate has probability `[b]`. -/
theorem prob_of_const (c : Call) (b : Bool) (h : ∀ z, c.predicate z = b) : c.prob = bitQ b := by
  rw [prob_eq_sum]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
  field_simp

/-- A predicate negated by an involution of the cube has probability `1/2`. -/
theorem prob_of_flip (c : Call) (f : BitInput c.n ≃ BitInput c.n) (h : ∀ z, c.predicate (f z) = !c.predicate z) :
    c.prob = 1 / 2 := by
  rw [prob_eq_sum]
  set S := ∑ z : BitInput c.n, bitQ (c.predicate z) with hS
  have hflip : S = ∑ z : BitInput c.n, (1 - bitQ (c.predicate z)) := by
    rw [hS, ← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [h z]
    cases c.predicate z <;> simp [bitQ]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube, mul_one, ← hS] at hflip
  have h2 : (2 : ℚ) ^ c.n ≠ 0 := by positivity
  rw [div_eq_iff h2]
  linarith

/-- **Exact evaluation for `W = 0`** (`sec:params`, paper/paper.tex): for a shaped call with no wires, the closed
form is the exact interval `(p_true, 0)`. -/
theorem closedValue_eq (c : Call) (hc : Shaped c) (hW : Transfer.callWires c = 0) :
    closedValue c = (c.prob, 0) := by
  have hW1 : Transfer.wires c.first = 0 := by unfold Transfer.callWires at hW; omega
  have hW2 : Transfer.wires c.second = 0 := by unfold Transfer.callWires at hW; omega
  have e1 := eval_of_gates_nil c.first hc.first_length (gates_nil_of_wires_zero c.first hW1)
  have e2 := eval_of_gates_nil c.second hc.second_length (gates_nil_of_wires_zero c.second hW2)
  unfold closedValue
  cases hk : c.kind with
  | single =>
    rw [prob_of_const c (constantValue c.first) (fun z => by unfold Call.predicate; rw [hk]; exact e1 z)]
  | pair =>
    rw [prob_of_const c (xor (constantValue c.first) (constantValue c.second))
      (fun z => by unfold Call.predicate; rw [hk]; simp only [e1 z, e2 z])]
  | parity =>
    simp only
    split_ifs with hodd
    · -- an index of odd multiplicity: flipping it negates the predicate
      unfold oddParity at hodd
      obtain ⟨i, hi, hcount⟩ := of_decide_eq_true hodd
      let i' : Fin c.n := ⟨i, Finset.mem_range.mp hi⟩
      let f : BitInput c.n ≃ BitInput c.n :=
        { toFun := fun z => Function.update z i' (!z i')
          invFun := fun z => Function.update z i' (!z i')
          left_inv := fun z => by funext j; by_cases hj : j = i' <;> simp [hj]
          right_inv := fun z => by funext j; by_cases hj : j = i' <;> simp [hj] }
      rw [prob_of_flip c f (fun z => by
        unfold Call.predicate
        rw [hk]
        simp only [e1]
        have hs := bitSign_parityOf_flip c i' hcount z
        change Sampler.bitSign (c.parityOf (f z)) = _ at hs
        cases hp : c.parityOf z <;> cases hq : c.parityOf (f z) <;>
          simp_all [Sampler.bitSign] <;> norm_num at hs)]
    · rw [prob_of_const c (constantValue c.first) (fun z => by
        unfold Call.predicate
        rw [hk]
        simp only [e1 z, parityOf_eq_false c (by simpa using hodd) z, Bool.xor_false])]

end NearQuarticWires.Builder
