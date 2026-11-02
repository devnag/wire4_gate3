import Proof.Quartic.StageMain.RuntimeWords
import Proof.Quartic.StageMain.RuntimeSizes

/-!
# Source-step count for the sampled main pass

`prop:time`, paper/paper.tex: finite-prefix
acquisition and final record printing have polynomial cost; the sample
body is charged once for each of the `2^(n-k) Q` iterations.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact Controller StageLift

theorem acquisition_arithmetic (c p h w l read S : ℕ) (hS : 1 ≤ S)
    (hc : c ≤ S) (hp : p ≤ S) (hh : h ≤ S) (hw : w ≤ S) (hl : l ≤ S)
    (hr : read ≤ 20000 * S ^ 2) :
    (3000 * (c + 1) ^ 3 + 4000 * (p + 1) ^ 2 + 12 * h + 11 * w + 40) +
      5 * l + (3000 * (c + 1) ^ 3 + 12 * c + read + 8 * w + 22) + 8 ≤ 100000 * S ^ 3 := by
  calc
    _ ≤ (3000 * (S + 1) ^ 3 + 4000 * (S + 1) ^ 2 + 12 * S + 11 * S + 40) +
        5 * S + (3000 * (S + 1) ^ 3 + 12 * S + 20000 * S ^ 2 + 8 * S + 22) + 8 := by gcongr
    _ ≤ _ := by
      have h2 : S ≤ S ^ 2 := Nat.le_self_pow (by decide) _
      have h3 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
      nlinarith only [hS, h2, h3]

theorem initializeCost_le (c : Call) (p : Cells.Parameters) (w : List Bool) (S : ℕ)
    (hS : 1 ≤ S) (hc : (compactInput c p w).length ≤ S)
    (hr : parameterReadCost p (compactInput c p w).length ≤ 20000 * S ^ 2) :
    initializeCost c p w (compactInput c p w).length ≤ 100000 * S ^ 3 := by
  obtain ⟨hcall, hp, hpre, hw⟩ := compact_lengths c p w
  exact acquisition_arithmetic _ _ _ _ _ _ S hS (hcall.trans hc) (hp.trans hc)
    (hpre.trans hc) (hw.trans hc) hc hr

theorem activeTailCost_le {B1 B2 : ℕ} (c : Call) (p : Program.Selected c)
    (w : List Bool) (T S : ℕ) (hS : 1 ≤ S) (hT : T ≤ 100 * S)
    (hc : (callWord c).length ≤ S) (he : p.1.ellf ≤ S)
    (hm : (Program.mainWord B1 B2 c w).length ≤ 400 * S) :
    activeTailCost (B1 := B1) (B2 := B2) c p w 46 T ≤
      2000000 * S * (2 ^ (c.n - p.1.k) * p.1.Q) := by
  let N := 2 ^ (c.n - p.1.k)
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hQ : 1 ≤ p.1.Q := by rw [(Cells.prepare_spec _ p.1 p.2).Q_eq]; exact Nat.one_le_two_pow
  have hNQ : N ≤ N * p.1.Q := Nat.le_mul_of_pos_right _ hQ
  have hSN : N ≤ S * (N * p.1.Q) := hNQ.trans (Nat.le_mul_of_pos_left _ hS)
  have hSS : S ≤ S * (N * p.1.Q) := Nat.le_mul_of_pos_right _ (by nlinarith)
  calc
    _ ≤ 46 + 291 + (19 * N + 188 * S + 329) +
        (N * (p.1.Q * (100 * S + 4) + 13) + 12) +
        (3 * (13 * (S + 70 * (400 * S) + 500 + 1) + 3) + 2) + 3 := by
      unfold activeTailCost fieldPrintBound
      gcongr
    _ ≤ _ := by change _ ≤ 2000000 * S * (N * p.1.Q); nlinarith

theorem sourceSteps_le {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) (T S : ℕ)
    (hS : 1 ≤ S) (hT : T ≤ 100 * S)
    (hc : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ S)
    (he : p.1.ellf ≤ S) (hm : (Program.mainWord B1 B2 c w).length ≤ 400 * S)
    (hr : parameterReadCost p.1 (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ 20000 * S ^ 2) :
    sourceSteps B1 B2 c w T ≤ 3000000 * S ^ 3 * (2 ^ (c.n - p.1.k) * p.1.Q) := by
  have hi := initializeCost_le c p.1 (Program.witnessPrefix c p.1 w) S hS hc hr
  have ht := activeTailCost_le (B1 := B1) (B2 := B2) c p w T S hS hT
    ((compact_lengths c p.1 (Program.witnessPrefix c p.1 w)).1.trans hc) he hm
  have hQ : 1 ≤ p.1.Q := by rw [(Cells.prepare_spec _ p.1 p.2).Q_eq]; exact Nat.one_le_two_pow
  have hN : 1 ≤ 2 ^ (c.n - p.1.k) := Nat.one_le_two_pow
  have h3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have hNQ : 1 ≤ 2 ^ (c.n - p.1.k) * p.1.Q := by nlinarith
  have hh := Nat.mul_le_mul_right (2 ^ (c.n - p.1.k) * p.1.Q) h3
  have hi' := Nat.mul_le_mul_left (S ^ 3) hNQ
  have hpos : 1 ≤ S ^ 3 := Nat.pow_pos hS
  simp only [sourceSteps, hd, activeAcquireCost]
  nlinarith

theorem extractFieldSteps_le {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) (S : ℕ)
    (hS : 1 ≤ S)
    (hc : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ S)
    (he : p.1.ellf ≤ S)
    (hr : parameterReadCost p.1 (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length ≤ 20000 * S ^ 2) :
    extractFieldSteps B1 B2 c w ≤ 101000 * S ^ 3 := by
  have hi := initializeCost_le c p.1 (Program.witnessPrefix c p.1 w) S hS hc hr
  have h3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  simp only [extractFieldSteps, hd, extractActiveCost]
  nlinarith

end NearQuarticWires.StageMain.Runtime
