import Proof.CaseAnalysis.FinalFuelRepin

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The defect: the POLYNOMIAL bucket can never hold one `2^q` call -/

/-- The polynomial fuel bound is eventually below `2 ^ q(N)`.
For every allowed coefficient `C` and degree `d <= k+1`, as in `Runtime.ha`
from `Proof/CaseAnalysis/FinalResidualLeaves.lean`, `polyFuel C d N` is
eventually strictly below `2 ^ q(N)`. The same degree restriction is used by
`runtime_of_polyFuel` in `Proof/CaseAnalysis/FinalFuelRepin.lean`.

One AND-four analysis call is charged `2^q/q^sigma`, with `q^sigma`
polylogarithmic in `N`. The proof below shows that an admissible `polyFuel`
does not pay for such a call. Once `C <= N`, one extra factor of `N+1`
absorbs the coefficient, and `pow_widthAt_ge` provides the remaining bound. 
-/
theorem envelope_defect (sources : EightSources) (k C d : ℕ) (hd : d ≤ k + 1) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → polyFuel C d N < 2 ^ widthAt sources k N := by
  refine ⟨C, ?_⟩
  intro N hN
  have hone : 1 ≤ N + 1 := by omega
  have hpos : 0 < (N + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have hdeg : (N + 1) ^ d ≤ (N + 1) ^ (k + 1) := Nat.pow_le_pow_right hone hd
  have hstep : C * (N + 1) ^ d < (N + 1) * (N + 1) ^ (k + 1) := by
    have h1 : C * (N + 1) ^ d ≤ C * (N + 1) ^ (k + 1) := Nat.mul_le_mul_left _ hdeg
    have h2 : C * (N + 1) ^ (k + 1) < (N + 1) * (N + 1) ^ (k + 1) :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) hpos
    omega
  have hgrow : (N + 1) * (N + 1) ^ (k + 1) ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := by
    have he : (N + 1) * (N + 1) ^ (k + 1) = (N + 1) ^ (k + 2) := by ring
    rw [he]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  calc polyFuel C d N = C * (N + 1) ^ d := rfl
    _ < (N + 1) * (N + 1) ^ (k + 1) := hstep
    _ ≤ 2 ^ 23 * (N + 1) ^ (k + 2) := hgrow
    _ ≤ 2 ^ widthAt sources k N := pow_widthAt_ge sources k N

/-! ## Section 2  The repair: the HOT bucket already holds it, and that is where it lands -/

/-- The same polynomial fuel fits one residual-table factor.
For `d + 1 <= k + 2`, `polyFuel C d N` is bounded by
`2 ^ (q - kappa * L_q)`, the cell permitted by `ledger_of_parts`'s `hrow`
binder in `Proof/CaseAnalysis/FinalLedgerAssembly.lean`.
The saving condition is `kappa >= h_D + sigma + c_1`.

`stageFuel_core` in `Proof/CaseAnalysis/FinalSupplierFuel.lean` routes the
analysis cost to that cell; the polynomial remainder pays the docked emit
and tail budget. Compare `rowFuel_le_table` in
`Proof/CaseAnalysis/FinalFuelRepin.lean`. 


-/
theorem polyFuel_le_table (sources : EightSources) (k r degree C d N : ℕ)
    (hd : d + 1 ≤ k + 2)
    (hN : repinOnset sources k r degree C ≤ N) :
    polyFuel C d N
      ≤ 2 ^ (widthAt sources k N
          - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1)) := by
  refine le_trans ?_ (rowFuel_le_table sources k r degree C d N hd hN)
  show polyFuel C d N ≤ 2 * polyFuel C d N + 2 * polyFuel C d N + 18
  omega

/-- **The two sections side by side**, at one instance: the same budget is below the residual
table factor and above nothing in the polynomial bucket reaches `2^q`.  Stated as one
conjunction so that a consumer cannot take half of it. -/
theorem envelope_split (sources : EightSources) (k r degree C d : ℕ) (hd : d + 1 ≤ k + 2) :
    (∃ onset : ℕ, ∀ N, onset ≤ N → polyFuel C d N < 2 ^ widthAt sources k N) ∧
    (∀ N, repinOnset sources k r degree C ≤ N →
      polyFuel C d N
        ≤ 2 ^ (widthAt sources k N
            - ledgerExponent sources r degree * (Nat.log 2 (widthAt sources k N) + 1))) :=
  ⟨envelope_defect sources k C d (by omega),
    fun N hN => polyFuel_le_table sources k r degree C d N hd hN⟩

end
end NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope
