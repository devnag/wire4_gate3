import Proof.Quartic.Worker.Prelude
import Proof.Quartic.Worker.Worker.Loop
import Proof.MachineModel.OrdinaryOracleComposeClock

/-!
# Worker.CounterDock for the weak machine of the wire measure

* `clock_runFrom`: **The clocked run.**.

Adapted from `Proof.Gates.Worker.CounterDock` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4`
(`NearQuarticWires.Worker4.Counter`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.Worker
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.OrdinaryOracleCompose

/-- **The clocked run.** -/
theorem clock_runFrom {t s : ℕ} (M : Machine t s) :
    ∀ (fuel : ℕ) (c : Configuration t s) (n : ℕ) (r : ExecutionReceipt t s), runFrom M fuel c = some r →
      ∃ r', runFrom (clockMachine M) fuel (clockConfig c n) = some r' ∧
        r'.final = clockConfig r.final (n + r.steps) ∧ r'.steps = r.steps
  | 0, c, n, r, hr => by
    by_cases hh : M.halted c.control = true
    · have hh' : (clockMachine M).halted (clockConfig c n).control = true := hh
      simp only [runFrom, hh, hh', if_true, Option.some.injEq] at hr ⊢
      subst hr
      exact ⟨_, rfl, by simp, rfl⟩
    · simp [runFrom, hh] at hr
  | fuel + 1, c, n, r, hr => by
    by_cases hh : M.halted c.control = true
    · have hh' : (clockMachine M).halted (clockConfig c n).control = true := hh
      simp only [runFrom, hh, hh', if_true, Option.some.injEq] at hr ⊢
      subst hr
      exact ⟨_, rfl, by simp, rfl⟩
    · have hh' : ¬ (clockMachine M).halted (clockConfig c n).control = true := hh
      cases hs : step M c with
      | none => simp [runFrom, hh, hs] at hr
      | some d =>
        cases ht : runFrom M fuel d with
        | none => simp [runFrom, hh, hs, ht] at hr
        | some tail =>
          simp only [runFrom, hh, hs, ht, Option.some.injEq, Bool.false_eq_true, if_false] at hr
          subst hr
          obtain ⟨tail', ht', hf, hst⟩ := clock_runFrom M fuel d (n + 1) tail ht
          refine ⟨⟨tail'.final, tail'.steps + 1, max (clockConfig c n).tapeCells tail'.peakTapeCells⟩, ?_, ?_, ?_⟩
          · simp only [runFrom, hh', clock_step M c d n hs, ht', Bool.false_eq_true, if_false]
          · simp only [hf]; congr 1; omega
          · simp [hst]

end NearQuarticWires.Worker4.Worker
