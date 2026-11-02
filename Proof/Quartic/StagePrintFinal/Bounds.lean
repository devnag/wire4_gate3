import Proof.Quartic.StagePrint.FinalPrintTarget
import Proof.Quartic.StageGreedyCollector.SourceLength
import Proof.Quartic.Control.GammaControl

/-!
# Selected printer budgets with one additive raw-index term

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the
selected original-column population is the unpadded center count. -/
def columns {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  2^(r.child.call.n-r.child.selected.1.k)

/-- `imp:partition` and `prop:time`, paper/paper.tex: the literal selected cell call and
the counter's original-column exponent have exactly the same census. -/
theorem columns_eq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.ncol=columns r := by rfl

/-- `prop:time`, paper/paper.tex: every
downstream carrier or native stage has original-column polynomial
cost independently of the once-read raw target-index representation. -/
def ColumnBound {B1 B2 : ℕ} (budget : Greedy.PrintRequest B1 B2→ℕ) : Prop :=
  ∃K e : ℕ,∀r,budget r≤K*columns r*(r.child.call.n+1)^e

/-- `prop:time`, paper/paper.tex: the
whole printer allows the original-column term and one additive
polynomial in the literal raw print-index length. -/
def PrintBound {B1 B2 : ℕ} (budget : Greedy.PrintRequest B1 B2→ℕ) : Prop :=
  ∃K e : ℕ,∀r,budget r≤K*(columns r*(r.child.call.n+1)^e+
    ((Greedy.printIndexWord r).length+1)^e)

/-- `prop:time`, paper/paper.tex: fixed
physical costs fit the original-column budget on every selected call. -/
theorem ColumnBound.const (B1 B2 m : ℕ) :
    ColumnBound (B1:=B1) (B2:=B2) (fun _=>m) := by
  refine ⟨m,0,fun r=>?_⟩
  simp only [pow_zero,Nat.mul_one]
  exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)

/-- `prop:time`, paper/paper.tex: a
smaller actual physical budget retains its selected column bound. -/
theorem ColumnBound.mono {B1 B2 : ℕ} {f g : Greedy.PrintRequest B1 B2→ℕ}
    (hg : ColumnBound g) (h : ∀r,f r≤g r) : ColumnBound f := by
  obtain ⟨K,e,hK⟩:=hg
  exact ⟨K,e,fun r=>(h r).trans (hK r)⟩

/-- `prop:time`, paper/paper.tex: a
fixed physical composition multiplier preserves the column budget. -/
theorem ColumnBound.scale {B1 B2 : ℕ} {f : Greedy.PrintRequest B1 B2→ℕ}
    (hf : ColumnBound f) (m : ℕ) : ColumnBound (fun r=>m*f r) := by
  obtain ⟨K,e,hK⟩:=hf
  refine ⟨m*K,e,fun r=>?_⟩
  exact (Nat.mul_le_mul_left m (hK r)).trans_eq (by ring)

/-- `prop:time`, paper/paper.tex: sums
of selected downstream clocks remain column-times-polynomial costs. -/
theorem ColumnBound.add {B1 B2 : ℕ} {f g : Greedy.PrintRequest B1 B2→ℕ}
    (hf : ColumnBound f) (hg : ColumnBound g) : ColumnBound (fun r=>f r+g r) := by
  obtain ⟨Kf,ef,hf⟩:=hf
  obtain ⟨Kg,eg,hg⟩:=hg
  refine ⟨Kf+Kg,ef+eg,fun r=>?_⟩
  have hbase : 1≤r.child.call.n+1:=by omega
  have h1:=(hf r).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hbase (Nat.le_add_right ef eg)))
  have h2:=(hg r).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hbase (Nat.le_add_left eg ef)))
  exact (Nat.add_le_add h1 h2).trans_eq (by ring)

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual framed computation
pays every output payload byte, including all zero entries. -/
theorem ColumnBound.output_payload {B1 B2 : ℕ}
    {input output : Greedy.PrintRequest B1 B2→List Bool} {budget : Greedy.PrintRequest B1 B2→ℕ}
    (f : WordFunction (Greedy.PrintRequest B1 B2) input (fun r=>frame (output r)) budget)
    (hb : ColumnBound budget) : ColumnBound (fun r=>(output r).length) := by
  apply ColumnBound.mono (hb.add (ColumnBound.const B1 B2 1))
  intro r
  have h:=Control.output_length_le f r
  rw [frame_length] at h
  omega

/-- `prop:time`, paper/paper.tex: an
actual linear carrier pass has a selected column budget using the
intermediate carrier census, without charging raw-index acquisition
again in the original-column term. -/
theorem ColumnBound.of_carrier {B1 B2 : ℕ} {budget : Greedy.PrintRequest B1 B2→ℕ}
    (hb : StageGreedyCollector.ContextBudgetBound budget) : ColumnBound budget :=
  StageGreedyCollector.context_budget_selected hb

/-- `prop:time`, paper/paper.tex: an
actual native-record map pays its input bytes and one real callee
clock at a fixed multiplier, preserving the selected column bound. -/
theorem ColumnBound.middle {B1 B2 : ℕ}
    {input output : Greedy.PrintRequest B1 B2→List Bool} {budget : Greedy.PrintRequest B1 B2→ℕ}
    (f : WordFunction (Greedy.PrintRequest B1 B2) input (fun r=>frame (output r)) budget)
    (modulus targetCount : Greedy.PrintRequest B1 B2→ℕ)
    (M : StagePrint.NativeMiddle.Mapper f modulus targetCount)
    (hi : ColumnBound (fun r=>(StagePrint.NativeMiddle.word (modulus r) (input r) (targetCount r)).length))
    (hb : ColumnBound budget) : ColumnBound M.budget := by
  obtain ⟨K,hK⟩:=M.linear_budget
  exact ColumnBound.mono (((hi.add hb).add (ColumnBound.const B1 B2 1)).scale K) hK

/-- `prop:time`, paper/paper.tex: a
pure downstream column budget introduces no raw-index multiplier
when combined with the whole printer's additive source allowance. -/
theorem ColumnBound.to_print {B1 B2 : ℕ} {f : Greedy.PrintRequest B1 B2→ℕ}
    (hf : ColumnBound f) : PrintBound f := by
  obtain ⟨K,e,hK⟩:=hf
  refine ⟨K,e,fun r=>?_⟩
  exact (hK r).trans (by
    have h:=Nat.mul_le_mul_left K (Nat.le_add_right
      (columns r*(r.child.call.n+1)^e) (((Greedy.printIndexWord r).length+1)^e))
    simpa only [Nat.mul_assoc] using h)

/-- `prop:time`, paper/paper.tex: a
smaller actual printer clock retains the same additive source bound. -/
theorem PrintBound.mono {B1 B2 : ℕ} {f g : Greedy.PrintRequest B1 B2→ℕ}
    (hg : PrintBound g) (h : ∀r,f r≤g r) : PrintBound f := by
  obtain ⟨K,e,hK⟩:=hg
  exact ⟨K,e,fun r=>(h r).trans (hK r)⟩

/-- `prop:time`, paper/paper.tex: fixed
ordinary composition factors preserve the additive raw-index term. -/
theorem PrintBound.scale {B1 B2 : ℕ} {f : Greedy.PrintRequest B1 B2→ℕ}
    (hf : PrintBound f) (m : ℕ) : PrintBound (fun r=>m*f r) := by
  obtain ⟨K,e,hK⟩:=hf
  exact ⟨m*K,e,fun r=>(Nat.mul_le_mul_left m (hK r)).trans_eq (by ring)⟩

/-- `prop:time`, paper/paper.tex: adding
selected stage clocks raises only fixed polynomial exponents; the
raw-index polynomial remains additive rather than column-multiplied. -/
theorem PrintBound.add {B1 B2 : ℕ} {f g : Greedy.PrintRequest B1 B2→ℕ}
    (hf : PrintBound f) (hg : PrintBound g) : PrintBound (fun r=>f r+g r) := by
  obtain ⟨Kf,ef,hf⟩:=hf
  obtain ⟨Kg,eg,hg⟩:=hg
  refine ⟨Kf+Kg,ef+eg,fun r=>?_⟩
  have hb : 1≤r.child.call.n+1:=by omega
  have hi : 1≤(Greedy.printIndexWord r).length+1:=by omega
  have h1:=(hf r).trans (Nat.mul_le_mul_left _ (Nat.add_le_add
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.le_add_right ef eg)))
    (Nat.pow_le_pow_right hi (Nat.le_add_right ef eg))))
  have h2:=(hg r).trans (Nat.mul_le_mul_left _ (Nat.add_le_add
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.le_add_left eg ef)))
    (Nat.pow_le_pow_right hi (Nat.le_add_left eg ef))))
  exact (Nat.add_le_add h1 h2).trans_eq (by ring)

end NearQuarticWires.StagePrintFinal
