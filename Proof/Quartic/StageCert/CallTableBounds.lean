import Proof.Quartic.StageCert.TableWidthBound
import Proof.Quartic.Cells.ParametersPrepWord

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic

/-- `prop:time`, paper/paper.tex: the scalar width envelope
is polynomial in the serialized call, uniformly over witness words. -/
def callTableWidthEnvelope (B1 : ℕ) (c : Call) : ℕ :=
  200*(preparationCoefficient B1+5)*((callWord c).length+1)^(B1+12)+
  (callWord c).length+4096*((callWord c).length+1)+
  100*(preparationCoefficient B1+1)^2*((callWord c).length+1)^(2*(B1+12))+8

/-- `prop:time`, paper/paper.tex: a dispatched column
contains linearly many strict tests in the original input arity. -/
theorem actual_columnRecords_length {c : Call} {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2^(c.n-p.k))) :
    (columnRecords p.k (Builder.columnData c hs w z)).length≤4096*(c.n+1) := by
  have hcore : Cells.CoreRules (Builder.callInput c) p := hs
  have hm : p.mu≤c.n := hcore.mu_le_lambda.trans hcore.lambda_le_n
  have hj := hs.J_bound
  rw [hs.Jmax_eq] at hj
  have hh := columnRecords_length_le p.k (Builder.columnData c hs w z)
  change _≤1+512*(p.J-1+2) at hh
  omega

/-- `prop:time`, paper/paper.tex: the actual certificate
record census is linear in the number of columns, with no hidden padded
walk or field enumeration. -/
theorem callTable_streamWork {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c=some p) (w : List Bool) :
    streamWork (callTableRequest B1 B2 c w).columns≤2^(c.n-p.1.k)*(4096*(c.n+1)+1) := by
  have hs := Cells.prepare_spec _ p.1 p.2
  let cols := (callTableRequest B1 B2 c w).columns
  have hc : cols=List.ofFn (fun z : Fin (2^(c.n-p.1.k)) =>
      columnRecords p.1.k (Builder.columnData c hs w z)) := by
    simp only [cols,callTableRequest,hd]
    rfl
  rw [show (callTableRequest B1 B2 c w).columns=cols from rfl,hc]
  have h := streamWork_le (List.ofFn (fun z : Fin (2^(c.n-p.1.k)) =>
      columnRecords p.1.k (Builder.columnData c hs w z))) (4096*(c.n+1)) (by
    intro rs hrs
    obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hrs
    exact actual_columnRecords_length hs w z)
  simpa only [List.length_ofFn] using h

/-- `prop:time`, paper/paper.tex: every actual signed-table
request has a polynomial arithmetic width before any certificate passes. -/
theorem callTable_width_le (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    tableWidth (callTableRequest B1 B2 c w)≤callTableWidthEnvelope B1 c := by
  classical
  have hp := Cells.all_calls_prepWord_length B1 B2 c w
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    have he : (callTableRequest B1 B2 c w).columns=[] := by simp [callTableRequest,hd]
    have hh := tableWidth_le (callTableRequest B1 B2 c w) 0 0 0
      (by rw [he]; simp) (by rw [he]; simp) (by rw [he]; simp)
    change tableWidth (callTableRequest B1 B2 c w)≤
      (Program.prepWord B1 B2 c w).length+0+0+0+8 at hh
    unfold callTableWidthEnvelope
    omega
  | some p =>
    let hs := Cells.prepare_spec _ p.1 p.2
    let K := certificateBitEnvelope (preparationEnvelope B1 c.n)
    have hn := Cells.dispatched_n_le_callWord hd
    have hb : 1≤c.radius*(c.n:ℚ)^B1 :=
      (Program.dispatch_admitted hd).1.2.2.2.2.2.2.2.2.2.1
    have he : (callTableRequest B1 B2 c w).columns=
        List.ofFn (fun z : Fin (2^(c.n-p.1.k)) =>
          columnRecords p.1.k (Builder.columnData c hs w z)) := by
      simp only [callTableRequest,hd]
      rfl
    have hcols : (callTableRequest B1 B2 c w).columns.length≤2^c.n := by
      rw [he,List.length_ofFn]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have hlen : ∀rs∈(callTableRequest B1 B2 c w).columns,rs.length≤4096*(c.n+1) := by
      rw [he]
      intro rs hrs
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hrs
      exact actual_columnRecords_length hs w z
    have hrec : ∀rs∈(callTableRequest B1 B2 c w).columns,∀t∈rs,
        |t.1|≤(2:ℤ)^K ∧ t.2≤2^K := by
      rw [he]
      intro rs hrs
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hrs
      exact columnRecords_selected_bound c hs B1 hb w z
    have hh := tableWidth_le (callTableRequest B1 B2 c w) c.n (4096*(c.n+1)) K
      hcols hlen hrec
    have hk := Cells.dispatched_certificate_bit_envelope hd
    change K≤_ at hk
    change tableWidth (callTableRequest B1 B2 c w)≤
      (Program.prepWord B1 B2 c w).length+c.n+4096*(c.n+1)+K+8 at hh
    unfold callTableWidthEnvelope
    omega

end NearQuarticWires.StageCert
