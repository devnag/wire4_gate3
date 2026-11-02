import Proof.Quartic.StageMain.RuntimeSource
import Proof.Quartic.StageMain.RuntimeCompile

/-!
# Arithmetic of the two-pass main clock

`prop:time`, paper/paper.tex, charges the
retained-input copy, one field search, the complete main arithmetic
program, and both framed handoffs. The field-search exponential is
kept separate from the sample census.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

theorem compiled_clock_arithmetic (A S N : ℕ) (hS : 1 ≤ S) (hN : 1 ≤ N) :
    10000 * S ^ 2 * (A * S ^ 3 * N + 25 * S * N + 1) ≤
      (10000 * (A + 26)) * S ^ 5 * N := by
  have h3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have hSN := Nat.mul_le_mul_right N h3
  have hpos : 1 ≤ S ^ 3 * N := Nat.mul_pos (Nat.pow_pos hS) hN
  calc
    _ ≤ 10000 * S ^ 2 * ((A + 26) * S ^ 3 * N) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by ring

theorem setup_clock_le (r : FieldRequest) :
    fieldSetupCost r ≤ 1000 * (2 ^ (2 * r.val) * (r.val + 1)) := by
  have hh : GF2.searchCost r.val ≤ 200 * (2 ^ (2 * r.val) * (r.val + 1)) := by
    simpa only [pow_one] using GF2.searchCost_le r.val (r.val + 1) (by omega) (by omega)
  have hp : 1 ≤ 2 ^ (2 * r.val) := Nat.one_le_two_pow
  have hmul : r.val + 1 ≤ 2 ^ (2 * r.val) * (r.val + 1) := Nat.le_mul_of_pos_left _ hp
  simp only [fieldSetupCost, fieldUnaryWord, List.length_replicate, PrimAsm.Modulus.modCost]
  omega

theorem composition_clock_arithmetic (X Y F I H S N E : ℕ)
    (hS : 1 ≤ S) (hN : 1 ≤ N) (hE : 1 ≤ E)
    (hX : X ≤ 2000000000 * S ^ 5 * N) (hY : Y ≤ 40000000000 * S ^ 5 * N)
    (hF : F ≤ 2000 * S * E) (hI : I ≤ 25 * S * N) (hH : H ≤ S) :
    4 * (2 * (2 * (4 * X + 4 * F + 12) + 150 * (I + H + 1)) + 2) + 4 * Y + 12 ≤
      10000000000000 * S ^ 5 * (N + E) := by
  have h5 : S ≤ S ^ 5 := Nat.le_self_pow (by decide) _
  have hSN := Nat.mul_le_mul_right N h5
  have hSE := Nat.mul_le_mul_right E h5
  have hNS : S ≤ S * N := Nat.le_mul_of_pos_right _ hN
  have hES : S ≤ S * E := Nat.le_mul_of_pos_right _ hE
  nlinarith only [hS, hX, hY, hF, hI, hH, hSN, hSE, hNS, hES]

end NearQuarticWires.StageMain.Runtime
