import Proof.Quartic.StageMain.RuntimeActive
import Proof.Quartic.StageMain.RuntimeDefault
import Proof.Quartic.StageMain.RuntimeParameterRead
import Proof.Quartic.StageMain.RuntimeEnvelope

/-!
# Ordinary main-stage cost in the paper's exact ledger

`prop:time`, paper/paper.tex: the actual composed
main machine pays all source parsing, allocation, field search, sample
calls, totals and serialization within the three-term envelope. A false
tag has constant cost. The constants are uniform over all calls and all
witness words for each fixed entry machine and its polynomial reservation.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open Runtime

def mainRuntimeDegree (B1 B2 d : ℕ) : ℕ := 5 * (mainSizeDegree B1 B2 d + 1)

noncomputable def mainRuntimeCoefficient {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ) : ℕ :=
  10000000000000 * (runtimeCoefficient f K d) ^ 5 * ledgerCoefficient (mainRuntimeDegree B1 B2 d)

theorem mainBudget_active_ledger {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    mainBudgetWithEntry f K d c w ≤ mainRuntimeCoefficient f K d *
      Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda
        (ledgerExponent B1 (mainRuntimeDegree B1 B2 d)) := by
  have hb := mainBudget_active_bound f K d hd w (selected_parameterReadCost f K d hd w)
  have hs := runtimeScale_polynomial f K d c.n
  have hc := selected_census_le hd (mainRuntimeDegree B1 B2 d)
  have hpoly (A n e N : ℕ) : 10000000000000 * (A * (n + 1) ^ e) ^ 5 * N =
      (10000000000000 * A ^ 5) * (N * (n + 1) ^ (5 * e)) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm e 5]
    ring
  calc
    _ ≤ 10000000000000 * (runtimeScale f K d c.n) ^ 5 *
        (2 ^ (c.n - p.1.k) * p.1.Q + 2 ^ (2 * p.1.ellf)) := hb
    _ ≤ 10000000000000 *
        (runtimeCoefficient f K d * (c.n + 1) ^ (mainSizeDegree B1 B2 d + 1)) ^ 5 *
        (2 ^ (c.n - p.1.k) * p.1.Q + 2 ^ (2 * p.1.ellf)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 5))
    _ = (10000000000000 * (runtimeCoefficient f K d) ^ 5) *
        ((2 ^ (c.n - p.1.k) * p.1.Q + 2 ^ (2 * p.1.ellf)) * (c.n + 1) ^ mainRuntimeDegree B1 B2 d) := by
      exact hpoly _ _ _ _
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_left (10000000000000 * (runtimeCoefficient f K d) ^ 5) hc
      simpa only [mainRuntimeCoefficient, Nat.mul_assoc] using hh

/-- Step 4 and `prop:time`, paper/paper.tex: the complete physical budget satisfies the exact all-call
ledger, independently of every witness and every decoded source value. -/
theorem mainBudget_ledger {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget) (K d : ℕ) :
    Program.LedgerCost B1 B2 (mainBudgetWithEntry f K d) := by
  let C := defaultClock f K d + mainRuntimeCoefficient f K d + 1
  let e := ledgerExponent B1 (mainRuntimeDegree B1 B2 d)
  refine ⟨C, e, ?_⟩
  intro c w
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    have h := mainBudget_none_le f K d hd w
    have hpow : 1 ≤ ((callWord c).length + 1) ^ e := Nat.pow_pos (Nat.succ_pos _)
    have hh : C ≤ C * ((callWord c).length + 1) ^ e := Nat.le_mul_of_pos_right _ hpow
    have hC : defaultClock f K d ≤ C := by dsimp only [C]; omega
    exact (h.trans (hC.trans hh)).trans (Nat.le_add_right _ _)
  | some p =>
    have h := mainBudget_active_ledger f K d hd w
    have heq : Program.runEnvelope B1 B2 e c =
        Machine.propTimeEnvelope c.n p.1.k p.1.Q p.1.Jmax p.1.lambda e := by
      simp only [Program.runEnvelope, hd]
    have hh : mainRuntimeCoefficient f K d * Program.runEnvelope B1 B2 e c ≤
        C * Program.runEnvelope B1 B2 e c := Nat.mul_le_mul_right _ (by dsimp only [C]; omega)
    rw [heq] at hh ⊢
    exact (h.trans hh).trans (Nat.le_add_left _ _)

end NearQuarticWires.StageMain
