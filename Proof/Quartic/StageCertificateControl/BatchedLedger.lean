import Proof.Quartic.StageCertificateControl.BitmapLedger

/-!
# The real counted native batch preserves the counter runtime ledger

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.ENP.TableSearch (PB)

/-- `prop:time`, paper/paper.tex: all work
apart from native-table execution is polynomial in the actual finite
test count, original preparation bytes and real count-program budget. -/
theorem batchScalarPolynomial {α : Type} {size T S C : α→ℕ}
    (hT : PB size T) (hS : PB size S) (hC : PB size C) :
    PB size (fun r => batchWorkBound (T r) (S r) (C r) 0) := by
  have hplus := hT.add (PB.const 1)
  have hsquare : PB size (fun r => (T r+1)^2) := by
    simpa only [pow_two] using hplus.mul hplus
  have hbody := ((PB.const 20000).mul hsquare).add
    ((PB.const 1000).mul (hS.add (PB.const 1)))
  have hloop := (hT.mul ((hT.mul hbody).add (PB.const 10))).add (PB.const 1)
  have hprefix := (((PB.const 400).mul ((hS.add hC).add (PB.const 1))).add
    ((PB.const 2000).mul hsquare)).add (PB.const 100)
  have hflat := ((PB.const 1000).mul ((hS.add hT).add (PB.const 1))).add
    ((PB.const 10000).mul hsquare)
  have hfinal := ((PB.const 2).mul (((hprefix.add hloop).add hflat).add (PB.const 2))).add
    (PB.const 2)
  simpa only [batchWorkBound,Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one] using hfinal

/-- `prop:time`, paper/paper.tex: the native
execution budget enters the exact batch majorant linearly, with only
a polynomial coefficient in the public test count. -/
theorem batchWorkBound_linear (T S C B : ℕ) :
    batchWorkBound T S C B=batchWorkBound T S C 0+2000*T*(T+1)*B := by
  unfold batchWorkBound
  ring

/-- `prop:time`, paper/paper.tex:
the actual scalar count, preparation bytes and count-program budget,
together with any proved whole-native-program ledger, bound all real
batch calls, cache bytes and final output work. -/
theorem batchWorkBound_ledger (B1 B2 : ℕ) (nativeBudget : Call→List Bool→ℕ)
    (hnative : Program.LedgerCost B1 B2 nativeBudget) :
    Program.LedgerCost B1 B2 (fun c w => batchWorkBound (countHeaderValue B1 B2 c)
      (countWord B1 B2 (c,w)).length (countHeaderBudget B1 B2 (c,w)) (nativeBudget c w)) := by
  let size (r : Call×List Bool) := (callWord r.1).length
  let T (r : Call×List Bool) := countHeaderValue B1 B2 r.1
  let S (r : Call×List Bool) := (countWord B1 B2 r).length
  let C (r : Call×List Bool) := countHeaderBudget B1 B2 r
  have hT : PB size T := by
    obtain ⟨K,e,hK⟩ := countHeaderValuePolyCost B1 B2
    exact ⟨K,e,fun r => hK r.1 r.2⟩
  have hS : PB size S := by
    exact ⟨200*(Cells.ParameterArithmetic.preparationCoefficient B1+5),B1+12,
      fun r => Cells.all_calls_prepWord_length B1 B2 r.1 r.2⟩
  have hC : PB size C := by
    obtain ⟨K,e,hK⟩ := countHeaderPolyCost B1 B2
    exact ⟨K,e,fun r => hK r.1 r.2⟩
  have hscalar : Program.PolyCost (fun c w => batchWorkBound (T (c,w)) (S (c,w)) (C (c,w)) 0) := by
    obtain ⟨K,e,hK⟩ := batchScalarPolynomial hT hS hC
    exact ⟨K,e,fun c w => hK (c,w)⟩
  have hcoefficient : Program.PolyCost (fun c w => 2000*T (c,w)*(T (c,w)+1)) := by
    obtain ⟨K,e,hK⟩ := ((PB.const 2000).mul hT).mul (hT.add (PB.const 1))
    exact ⟨K,e,fun c w => hK (c,w)⟩
  have hsum := Greedy.LedgerCost.add (Greedy.LedgerCost.of_poly hscalar)
    (Greedy.LedgerCost.mul_poly hcoefficient hnative)
  refine StageCert.ledger_mono hsum ?_
  intro c w
  dsimp only [T,S,C]
  rw [batchWorkBound_linear]

/-- `prop:time`, paper/paper.tex:
the proved physical counted-batch budget inherits the original-source
ledger of its actual whole-table program, including all output bytes. -/
theorem batchedMachine_ledger {I : Type} {input payload : I→List Bool} {budget : I→ℕ}
    (B1 B2 : ℕ) (provider : WordFunction I input (fun r => frame (payload r)) budget)
    (families : Call→List Bool→StagePrint.PoolFamily I input)
    (hsource : ∀c w,(families c w).source=countWord B1 B2 (c,w))
    (hcount : ∀c w,(families c w).count=countHeaderValue B1 B2 c)
    (nativeBudget : Call→List Bool→ℕ)
    (hbudget : ∀c w j,budget ((families c w).request j)≤nativeBudget c w)
    (hnative : Program.LedgerCost B1 B2 nativeBudget) :
    Program.LedgerCost B1 B2 (fun c w => batchedMachineBudget (families c w) payload budget
      (countHeaderBudget B1 B2 (c,w))) := by
  refine StageCert.ledger_mono (batchWorkBound_ledger B1 B2 nativeBudget hnative) ?_
  intro c w
  have h := batchedMachineBudget_le provider (families c w) (countHeaderBudget B1 B2 (c,w))
    (nativeBudget c w) (hbudget c w)
  simpa only [hsource,hcount] using h

end NearQuarticWires.StageCertificateControl
