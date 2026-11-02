import Proof.Quartic.StageMain.CompactInitialize
import Proof.Quartic.StageMain.CallSize
import Proof.Quartic.Cells.ParametersPrepWord

/-!
# Polynomial capacity for the finite main prefix

`prop:time`, paper/paper.tex: the original call,
parameters and witness prefix have polynomial length in the arity.
The actual leading arity field therefore supplies the arithmetic width
without using the exponentially long certificate suffix.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Cells
open StageLift

def capacityCoefficient (B1 : ℕ) : ℕ :=
  200 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 5) * 1002 ^ (B1 + 12)

def capacityExponent (B1 B2 : ℕ) : ℕ := (B2 + 8) * (B1 + 12)

def widthAt (B1 B2 n : ℕ) : ℕ :=
  2 ^ (capacityExponent B1 B2 * (1 + natBitLength n)) * (capacityCoefficient B1 + 3)

theorem compactInput_length_arity {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤
      capacityCoefficient B1 * (c.n + 1) ^ capacityExponent B1 B2 := by
  have hc := CallSize.dispatched_callWord_polynomial hd
  have hp : (Program.prepWord B1 B2 c w).length ≤
      200 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12) :=
    Cells.dispatched_prepWord_length hd w
  have hone : 1 ≤ (c.n + 1) ^ (B2 + 8) := Nat.pow_pos (Nat.succ_pos _)
  have hc' : (callWord c).length + 1 ≤ 1002 * (c.n + 1) ^ (B2 + 8) := by omega
  rw [prepWord_eq_compact hd] at hp
  calc
    _ ≤ 200 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12) := hp
    _ ≤ 200 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 5) *
        (1002 * (c.n + 1) ^ (B2 + 8)) ^ (B1 + 12) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc' _)
    _ = _ := by simp only [mul_pow, ← pow_mul, capacityCoefficient, capacityExponent]; ring

theorem compactInput_width {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length + 2 ≤ widthAt B1 B2 c.n := by
  have h := compactInput_length_arity hd w
  have hn : c.n + 1 ≤ 2 ^ (1 + natBitLength c.n) := by
    have hn' := lt_natBitLength c.n
    have hm := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show natBitLength c.n ≤ 1 + natBitLength c.n by omega)
    omega
  have hp : (c.n + 1) ^ capacityExponent B1 B2 ≤
      2 ^ (capacityExponent B1 B2 * (1 + natBitLength c.n)) := by
    calc
      _ ≤ (2 ^ (1 + natBitLength c.n)) ^ capacityExponent B1 B2 := Nat.pow_le_pow_left hn _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  have hh := h.trans (Nat.mul_le_mul_left (capacityCoefficient B1) hp)
  have hpos : 1 ≤ (2 : ℕ) ^ (capacityExponent B1 B2 * (1 + natBitLength c.n)) :=
    Nat.pow_pos (by decide)
  unfold widthAt
  nlinarith

theorem natWord_length_mem (v : ℕ) (values : List ℕ) (hv : v ∈ values) :
    (natWord v).length ≤ (values.flatMap natWord).length := by
  induction values with
  | nil => simp at hv
  | cons x xs ih =>
    rcases List.mem_cons.1 hv with rfl | hv
    · simp only [List.flatMap_cons, List.length_append]
      omega
    · have h := ih hv
      simp only [List.flatMap_cons, List.length_append]
      omega

theorem parameter_bitLength_le_word (p : Cells.Parameters) (value : ℕ)
    (hv : value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++ parameterTailFields p ++ p.factors) :
    natBitLength value ≤ (Program.parametersWord p).length := by
  have h := (NearCubicGates.Close.Dispatch.natBitLength_le_len value).trans (natWord_length_mem value _ hv)
  have heq : (parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++ parameterTailFields p ++ p.factors).flatMap
      natWord = Program.parametersWord p := by
    rw [parametersWord_field_layout]
    simp only [List.flatMap_append, List.append_assoc]
  rwa [heq] at h

theorem compact_decoder_bounds (c : Call) (p : Cells.Parameters) (witness : List Bool) (W : ℕ)
    (hW : (compactInput c p witness).length + 2 ≤ W) :
    (preparedPrefixWord c p).length + 2 ≤ W ∧
    (compactInput c p witness).length < 2 ^ W ∧
    (∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++ parameterTailFields p ++ p.factors,
      natBitLength value ≤ (compactInput c p witness).length) ∧
    p.primes.card < 2 ^ W ∧ p.factors.length < 2 ^ W := by
  have hparam : (Program.parametersWord p).length ≤ (compactInput c p witness).length := by
    simp only [compactInput, preparedPrefixWord, List.length_cons, List.length_append]
    omega
  have hbits : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++ parameterTailFields p ++ p.factors,
      natBitLength value ≤ (compactInput c p witness).length :=
    fun value hv => (parameter_bitLength_le_word p value hv).trans hparam
  have hprime := hbits p.primes.card (by simp [parameterHeadFields])
  have hfactor := hbits p.factors.length (by simp [parameterTailFields])
  refine ⟨?_, ?_, hbits, ?_, ?_⟩
  · simp only [compactInput, List.length_append] at hW
    omega
  · exact lt_trans (by omega) Nat.lt_two_pow_self
  · exact (lt_natBitLength p.primes.card).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  · exact (lt_natBitLength p.factors.length).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))

end NearQuarticWires.StageMain.Compact
