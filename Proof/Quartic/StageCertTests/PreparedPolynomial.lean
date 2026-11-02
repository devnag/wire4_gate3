import Proof.Quartic.StageCertTests.PrepScheduleMachine
import Proof.Quartic.Cells.ParametersPrepWord

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex:
a direct preparation-source component has polynomial cost in
the literal original call word, uniformly over all witness words. -/
def PreparedPolynomial {B1 B2 : ℕ} (f : PreparedScheduleRequest B1 B2 → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ r, f r ≤ K*((callWord r.call).length+1)^e

variable {B1 B2 : ℕ}

/-- `prop:time`, paper/paper.tex: fixed costs
are polynomial in every actual original call word. -/
theorem PreparedPolynomial.const (value : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun _ => value) := by
  exact ⟨value,0,by intro r;simp⟩

/-- `prop:time`, paper/paper.tex: sums of
actual polynomial original-source costs remain polynomial. -/
theorem PreparedPolynomial.add {f g : PreparedScheduleRequest B1 B2 → ℕ}
    (hf : PreparedPolynomial f) (hg : PreparedPolynomial g) :
    PreparedPolynomial (fun r => f r+g r) := by
  obtain ⟨Kf,ef,hf⟩ := hf
  obtain ⟨Kg,eg,hg⟩ := hg
  refine ⟨Kf+Kg,ef+eg,fun r => ?_⟩
  have hX : 1 ≤ (callWord r.call).length+1 := by omega
  have h1 := Nat.mul_le_mul_left Kf (Nat.pow_le_pow_right hX (Nat.le_add_right ef eg))
  have h2 := Nat.mul_le_mul_left Kg (Nat.pow_le_pow_right hX (Nat.le_add_left eg ef))
  have h3 := hf r
  have h4 := hg r
  nlinarith

/-- `prop:time`, paper/paper.tex: products of
actual polynomial original-source costs remain polynomial. -/
theorem PreparedPolynomial.mul {f g : PreparedScheduleRequest B1 B2 → ℕ}
    (hf : PreparedPolynomial f) (hg : PreparedPolynomial g) :
    PreparedPolynomial (fun r => f r*g r) := by
  obtain ⟨Kf,ef,hf⟩ := hf
  obtain ⟨Kg,eg,hg⟩ := hg
  refine ⟨Kf*Kg,ef+eg,fun r => ?_⟩
  calc
    f r*g r ≤ (Kf*((callWord r.call).length+1)^ef)*(Kg*((callWord r.call).length+1)^eg) :=
      Nat.mul_le_mul (hf r) (hg r)
    _ = _ := by rw [pow_add];ring

/-- `prop:time`, paper/paper.tex: fixed powers
of actual polynomial original-source costs remain polynomial. -/
theorem PreparedPolynomial.pow {f : PreparedScheduleRequest B1 B2 → ℕ}
    (hf : PreparedPolynomial f) (n : ℕ) : PreparedPolynomial (fun r => (f r)^n) := by
  obtain ⟨K,e,hf⟩ := hf
  refine ⟨K^n,e*n,fun r => ?_⟩
  have h := Nat.pow_le_pow_left (hf r) n
  simpa only [mul_pow,←pow_mul] using h

/-- `prop:time`, paper/paper.tex: a component
below a proved polynomial actual cost inherits that cost bound. -/
theorem PreparedPolynomial.mono {f g : PreparedScheduleRequest B1 B2 → ℕ}
    (hg : PreparedPolynomial g) (hle : ∀ r, f r ≤ g r) : PreparedPolynomial f := by
  obtain ⟨K,e,hg⟩ := hg
  exact ⟨K,e,fun r => (hle r).trans (hg r)⟩

/-- `prop:time`, paper/paper.tex: actual source
call length is itself a polynomial cost. -/
theorem PreparedPolynomial.callLength :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => (callWord r.call).length) :=
  ⟨1,1,by intro r;simp⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: the complete actual parameter serialization has
polynomial length in its dispatched original call. -/
theorem PreparedPolynomial.parameterLength : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => (Program.parametersWord r.selected.1).length) := by
  refine ⟨100*(Cells.ParameterArithmetic.preparationCoefficient B1+4),B1+12,fun r => ?_⟩
  exact Cells.dispatched_parametersWord_length r.dispatched

/-- `sec:params` and `prop:time`, paper/paper.tex: the actual small scheduling width has polynomial
height in the original source call. -/
theorem PreparedPolynomial.hint : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => scheduleHint r.selected.1) :=
  ⟨scheduleWidthCoefficient B1,2*(B1+12),fun r => dispatched_scheduleHint_word r.dispatched⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: each retained scheduler scalar has a polynomial
numeric bound from the original dispatched parameter rules. -/
theorem PreparedPolynomial.scalar (field : ScheduleField) : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => field.value r.selected.1) := by
  refine ⟨Cells.ParameterArithmetic.preparationCoefficient B1,B1+12,fun r => ?_⟩
  have hs := Cells.prepare_spec _ r.selected.1 r.selected.2
  have hadm := (Program.dispatch_admitted r.dispatched).1
  have hb : 1 ≤ r.call.radius*(r.call.n:ℚ)^B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hbds := hs.scalar_preparation_bounds B1 hb
  have hv : field.value r.selected.1 ≤ Cells.ParameterArithmetic.preparationEnvelope B1 r.call.n := by
    cases field
    · exact hbds.k
    · exact hbds.Xmax
    · exact hbds.hE
    · exact hbds.J
    · exact hbds.Lambda
  exact hv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Cells.dispatched_n_le_callWord r.dispatched) 1) _))

/-- `prop:time`, paper/paper.tex: copying the
entire true preparation source remains polynomial for every witness. -/
theorem PreparedPolynomial.inputLength :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => r.word.length) := by
  refine ⟨200*(Cells.ParameterArithmetic.preparationCoefficient B1+5),B1+12,fun r => ?_⟩
  exact Cells.all_calls_prepWord_length B1 B2 r.call r.witness

end NearQuarticWires.StageCertTests
