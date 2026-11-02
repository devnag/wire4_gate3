import Proof.Quartic.StageMain.MainSizes
import Proof.Quartic.StageMain.CompilerRuntime
import Proof.Gates.CounterMachine.PrefixFinal

/-!
# Polynomial size of the main arithmetic reservations

`prop:time`, paper/paper.tex: a width initialized
from the unary length of the binary arity header remains polynomial
in that arity. Fixed machine dimensions and both compiled stages are
included in the common bound below.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CounterMachine.PrefixProg
open Compact Bounds StageLift

theorem header_power_le (a e n : ℕ) :
    2 ^ (e * (1 + natBitLength n)) * a ≤ (a * 4 ^ e) * (n + 1) ^ e := by
  have hh : 2 ^ (1 + natBitLength n) ≤ 4 * (n + 1) := by
    rw [pow_add]
    have := pow_nbl_le n
    norm_num only [pow_one] at *
    omega
  calc
    _ = (2 ^ (1 + natBitLength n)) ^ e * a := by rw [← pow_mul, Nat.mul_comm e]
    _ ≤ (4 * (n + 1)) ^ e * a := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hh _)
    _ = _ := by rw [mul_pow]; ring

theorem extraction_width_le (B1 B2 K d L : ℕ) :
    (fieldExtractSizes B1 B2).W L ≤ (mainSizes B1 B2 K d).W L := by
  have ha : capacityCoefficient B1 + 3 ≤ mainSizeCoefficient B1 K := by
    have hc : capacityCoefficient B1 + 3 ≤ coefficient B1 K := by unfold coefficient; omega
    have hpos : 1 ≤ coefficient B1 K := by unfold coefficient; omega
    unfold mainSizeCoefficient
    nlinarith
  have hd : capacityExponent B1 B2 ≤ mainSizeDegree B1 B2 d := by
    unfold mainSizeDegree degree
    omega
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right L hd)) ha

noncomputable def runtimeScale {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d n : ℕ) : ℕ :=
  (mainSizes B1 B2 K d).W (1 + natBitLength n) + mainSizeDegree B1 B2 d +
    TSK (sampleTaggedCallee f) + TSK StageGamma.fieldProducerCallee + VV + MM + n + 1000

noncomputable def runtimeCoefficient {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ) : ℕ :=
  mainSizeCoefficient B1 K * 4 ^ mainSizeDegree B1 B2 d + mainSizeDegree B1 B2 d +
    TSK (sampleTaggedCallee f) + TSK StageGamma.fieldProducerCallee + VV + MM + 1002

theorem runtimeScale_polynomial {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d n : ℕ) :
    runtimeScale f K d n ≤ runtimeCoefficient f K d * (n + 1) ^ (mainSizeDegree B1 B2 d + 1) := by
  have hw := header_power_le (mainSizeCoefficient B1 K) (mainSizeDegree B1 B2 d) n
  have hp : (n + 1) ^ mainSizeDegree B1 B2 d ≤ (n + 1) ^ (mainSizeDegree B1 B2 d + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (mainSizeDegree B1 B2 d + 1) := Nat.le_self_pow (by omega) _
  have hconst : 1 ≤ (n + 1) ^ (mainSizeDegree B1 B2 d + 1) := Nat.pow_pos (Nat.succ_pos _)
  have hw' := hw.trans (Nat.mul_le_mul_left (mainSizeCoefficient B1 K * 4 ^ mainSizeDegree B1 B2 d) hp)
  change (mainSizes B1 B2 K d).W (1 + natBitLength n) ≤ _ at hw'
  unfold runtimeScale runtimeCoefficient
  nlinarith

theorem runtimeScale_envelope {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d n : ℕ) :
    envelope B1 B2 K d n ≤ runtimeScale f K d n := by
  have hh := mainSizes_arity B1 B2 K d n
  have hp := envelope_pos B1 B2 K d n
  unfold runtimeScale
  nlinarith

end NearQuarticWires.StageMain.Runtime
