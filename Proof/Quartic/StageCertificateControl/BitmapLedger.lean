import Proof.Quartic.StageCertificateControl.BitmapCompiledCost
import Proof.Quartic.StageCert.CallLedger

/-!
# The complete signed bitmap consumer satisfies the counter ledger

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex:
uniformly over every literal signed batch satisfying the public shape
and width conditions, the actual cold bitmap compiler has the declared
original-call and three-term runtime bound, without a certificate premise. -/
theorem bitmapBudget_uniform_ledger (B1 B2 coefficient degree : ℕ) :
    ∃A E : ℕ,∀r : BitmapRequest B1 B2 coefficient degree,
      r.budget≤A*((callWord r.call).length+1)^E+A*Program.runEnvelope B1 B2 E r.call := by
  obtain ⟨K,e,hselected⟩ := bitmapBudget_selected_polynomial B1 B2 coefficient degree
  obtain ⟨K0,e0,hdefault⟩ := bitmapBudget_default_polynomial B1 B2 coefficient degree
  let majorant (c : Call) (_ : List Bool) :=
    ((K0+3*K)*((callWord c).length+1)^(e0+e))*(StageCert.actualColumnCount B1 B2 c+1)
  have hc : Program.LedgerCost B1 B2 (fun c (_ : List Bool) => StageCert.actualColumnCount B1 B2 c+1) :=
    Greedy.LedgerCost.add (StageCert.actualColumnCount_ledger B1 B2)
      (Greedy.LedgerCost.of_poly (by exact ⟨1,0,fun _ _ => by simp⟩))
  have hp : Program.PolyCost (fun c (_ : List Bool) =>
      (K0+3*K)*((callWord c).length+1)^(e0+e)) := ⟨K0+3*K,e0+e,fun _ _ => le_rfl⟩
  have hm : Program.LedgerCost B1 B2 majorant := Greedy.LedgerCost.mul_poly hp hc
  obtain ⟨A,E,hA⟩ := hm
  refine ⟨A,E,fun r => ?_⟩
  have hbase : 1≤(callWord r.call).length+1 := by omega
  have hbound : r.budget ≤ majorant r.call r.witness := by
    cases hd : Program.dispatch B1 B2 r.call with
    | none =>
      have h := hdefault r hd
      have hpow := Nat.pow_le_pow_right hbase (by omega : e0≤e0+e)
      have hh := Nat.mul_le_mul (by omega : K0≤K0+3*K) hpow
      change r.budget≤((K0+3*K)*((callWord r.call).length+1)^(e0+e))*
        (StageCert.actualColumnCount B1 B2 r.call+1)
      simp only [StageCert.actualColumnCount,hd,zero_add,mul_one]
      exact h.trans hh
    | some p =>
      have h := hselected r p hd
      have hn := paddedCount_le_two_centers r.call.n p.1.k
      have hpow := Nat.pow_le_pow_right hbase (by omega : e≤e0+e)
      have hcoefficient : K*(paddedCount r.call.n p.1.k+1)≤
          (K0+3*K)*(centerCount r.call.n p.1.k+1) := by nlinarith
      have hh := Nat.mul_le_mul hcoefficient hpow
      refine h.trans (hh.trans_eq ?_)
      dsimp only [majorant]
      simp only [StageCert.actualColumnCount,hd,centerCount]
      ring
  exact hbound.trans (hA r.call r.witness)

/-- `prop:time`, paper/paper.tex:
an actual source-to-native constructor inherits the proved bitmap
ledger by supplying its literal original-call identity. -/
theorem bitmapBudget_ledger {B1 B2 coefficient degree : ℕ}
    (requests : Call→List Bool→BitmapRequest B1 B2 coefficient degree)
    (hcall : ∀c w,(requests c w).call=c) :
    Program.LedgerCost B1 B2 (fun c w => (requests c w).budget) := by
  obtain ⟨K,e,hK⟩ := bitmapBudget_uniform_ledger B1 B2 coefficient degree
  refine ⟨K,e,fun c w => ?_⟩
  have h := hK (requests c w)
  simpa only [hcall] using h

end NearQuarticWires.StageCertificateControl
