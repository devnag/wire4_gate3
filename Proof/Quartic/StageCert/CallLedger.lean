import Proof.Quartic.StageCert.CallTableBounds
import Proof.Quartic.StageCert.FinishCost
import Proof.Quartic.Greedy.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program
open Cells.ParameterArithmetic

/-- `prop:time`, paper/paper.tex: the polynomial bound on
the complete scalar width has an exponent fixed before the input call. -/
theorem tableWidth_polyCost (B1 B2 : ℕ) :
    PolyCost (fun c w => tableWidth (callTableRequest B1 B2 c w)+1) := by
  let C := preparationCoefficient B1
  let E := 2*(B1+12)
  refine ⟨200*(C+5)+4096+100*(C+1)^2+10,E,?_⟩
  intro c w
  let X := (callWord c).length+1
  have hx : 1≤X := by dsimp [X]; omega
  have he : 1≤E := by dsimp [E]; omega
  have hp : 1≤X^E := Nat.one_le_pow _ _ hx
  have hlin : X≤X^E := by simpa only [pow_one] using Nat.pow_le_pow_right hx he
  have hsmall : X^(B1+12)≤X^E := Nat.pow_le_pow_right hx (by dsimp [E]; omega)
  have h := callTable_width_le B1 B2 c w
  unfold callTableWidthEnvelope at h
  change tableWidth (callTableRequest B1 B2 c w)≤
    200*(C+5)*X^(B1+12)+(callWord c).length+4096*X+100*(C+1)^2*X^E+8 at h
  have h1 := Nat.mul_le_mul_left (200*(C+5)) hsmall
  have h2 := Nat.mul_le_mul_left 4096 hlin
  have h3 : (callWord c).length≤X^E := (Nat.le_succ _).trans hlin
  change tableWidth (callTableRequest B1 B2 c w)+1 ≤
    (200*(C+5)+4096+100*(C+1)^2+10)*X^E
  nlinarith only [h,h1,h2,h3,hp]

/-- `prop:time`, paper/paper.tex: a pointwise smaller
physical cost inherits the same call-word and three-term runtime ledger. -/
theorem ledger_mono {B1 B2 : ℕ} {f g : Call→List Bool→ℕ}
    (hg : LedgerCost B1 B2 g) (h : ∀c w,f c w≤g c w) : LedgerCost B1 B2 f := by
  obtain ⟨K,e,hg⟩ := hg
  exact ⟨K,e,fun c w => (h c w).trans (hg c w)⟩

/-- `sec:algorithm`, paper/paper.tex: the exact original-column
count is zero on nondispatched calls and never depends on a witness suffix. -/
noncomputable def actualColumnCount (B1 B2 : ℕ) (c : Call) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 0
  | some p => 2^(c.n-p.1.k)

/-- `prop:time`, paper/paper.tex: one scan per original
column is already a term in the declared Step 2 runtime envelope. -/
theorem actualColumnCount_ledger (B1 B2 : ℕ) :
    LedgerCost B1 B2 (fun c _ => actualColumnCount B1 B2 c) := by
  refine ⟨1,0,?_⟩
  intro c w
  cases hd : Program.dispatch B1 B2 c with
  | none => simp [actualColumnCount,hd]
  | some p =>
    have hn : 1≤c.n := by have := (Program.dispatch_admitted hd).1.1; omega
    have hp : 1≤c.n^(2*p.1.Jmax) := Nat.one_le_pow _ _ hn
    have hcount : actualColumnCount B1 B2 c≤runEnvelope B1 B2 0 c := by
      simp only [actualColumnCount,runEnvelope,hd,Machine.propTimeEnvelope,Nat.add_zero,Nat.zero_mul,pow_zero,Nat.mul_one]
      have h := Nat.mul_le_mul_left (2^(c.n-p.1.k)) hp
      simp only [Nat.mul_one] at h
      exact h.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    simpa only [Nat.one_mul,pow_zero] using hcount.trans (Nat.le_add_left _ 1)

/-- `prop:time`, paper/paper.tex: the complete signed
moment-record census satisfies the source ledger, including every bad column. -/
theorem callTable_streamWork_ledger (B1 B2 : ℕ) :
    LedgerCost B1 B2 (fun c w => streamWork (callTableRequest B1 B2 c w).columns) := by
  have hf : PolyCost (fun c (_ : List Bool) => 4096*((callWord c).length+1)+1) := by
    refine ⟨4097,1,?_⟩
    intro c w
    simp only [pow_one]
    omega
  have hh := Greedy.LedgerCost.mul_poly hf (actualColumnCount_ledger B1 B2)
  refine ledger_mono hh ?_
  intro c w
  cases hd : Program.dispatch B1 B2 c with
  | none => simp [callTableRequest,hd,streamWork,actualColumnCount]
  | some p =>
    have hn := Cells.dispatched_n_le_callWord hd
    have h := callTable_streamWork hd w
    have hm : 4096*(c.n+1)+1≤4096*((callWord c).length+1)+1 := by omega
    calc
      streamWork (callTableRequest B1 B2 c w).columns≤2^(c.n-p.1.k)*(4096*(c.n+1)+1) := h
      _≤2^(c.n-p.1.k)*(4096*((callWord c).length+1)+1) := Nat.mul_le_mul_left _ hm
      _=(4096*((callWord c).length+1)+1)*actualColumnCount B1 B2 c := by
        simp only [actualColumnCount,hd]
        ring

/-- `prop:time`, paper/paper.tex: the exact finisher of
signed tables has the declared source runtime ledger, with its complete
physical compiler budget and no certificate premise. -/
theorem finishCallCost (B1 B2 : ℕ) :
    LedgerCost B1 B2 (fun c w => finishBudget (callTableRequest B1 B2 c w)) := by
  obtain ⟨K,hK⟩ := finishBudget_polynomial
  have hp : PolyCost (fun c w => (Program.prepWord B1 B2 c w).length) :=
    ⟨200*(preparationCoefficient B1+5),B1+12,Cells.all_calls_prepWord_length B1 B2⟩
  have h1 : PolyCost (fun (_ : Call) (_ : List Bool) => 1) := ⟨1,0,by intros; simp⟩
  have hbase := Greedy.LedgerCost.add
    (Greedy.LedgerCost.add (Greedy.LedgerCost.of_poly hp) (callTable_streamWork_ledger B1 B2))
    (Greedy.LedgerCost.of_poly h1)
  obtain ⟨C,e,hC⟩ := tableWidth_polyCost B1 B2
  have hwidth : PolyCost (fun c w => K*(tableWidth (callTableRequest B1 B2 c w)+1)^4) := by
    refine ⟨K*C^4,4*e,?_⟩
    intro c w
    have h := Nat.mul_le_mul_left K (Nat.pow_le_pow_left (hC c w) 4)
    simpa only [mul_pow,←pow_mul,Nat.mul_comm e 4,Nat.mul_assoc] using h
  have hall := Greedy.LedgerCost.mul_poly hwidth hbase
  refine ledger_mono hall ?_
  intro c w
  have h := hK (callTableRequest B1 B2 c w)
  change finishBudget (callTableRequest B1 B2 c w)≤
    K*((Program.prepWord B1 B2 c w).length+streamWork (callTableRequest B1 B2 c w).columns+1)*
      (tableWidth (callTableRequest B1 B2 c w)+1)^4 at h
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

end NearQuarticWires.StageCert
