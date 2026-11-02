import Proof.Quartic.StageCertificateControl.BitmapSourceCost

/-!
# Complete compiled bitmap work on selected and default inputs

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CellsPack (Gof)
open StageCertTests (PreparedPolynomial PreparedScheduleRequest)

/-- `prop:time`, paper/paper.tex: the actual
compiler setup, all signed source work and complete literal input copy
cost one native census times a fixed scalar-mass power. -/
theorem bitmapBudget_of_scalar_bounds {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) (M : ℕ) (h : BitmapScalarBounds r p M) :
    r.budget≤10^15*(paddedCount r.call.n p.1.k+1)*M^5 := by
  let N := paddedCount r.call.n p.1.k
  have hs := bitmapSourceSteps_scalar_bound r p hd M h
  have hw := bitmapInputLength_scalar_bound r p hd M h
  have hp : 1≤M^3 := Nat.one_le_pow _ _ (by have := h.positive;omega)
  have hpN : 1≤(N+1)*M^3 := by
    calc
      1≤N+1 := by omega
      _ ≤ (N+1)*M^3 := by simpa only [mul_one] using Nat.mul_le_mul_left (N+1) hp
  have hs' : r.sourceSteps+1≤100001*(N+1)*M^3 := by
    change r.sourceSteps≤100000*(N+1)*M^3 at hs
    nlinarith only [hs,hpN]
  have hg := Nat.pow_le_pow_left h.compilation 2
  have hm := Nat.mul_le_mul hs' hg
  have hm' : (r.sourceSteps+1)*
      Gof StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) (leadOnes r.word)^2≤
      100001*(N+1)*M^5 := hm.trans_eq (by ring)
  have hpow := Nat.pow_le_pow_right (by have := h.positive;omega : 1≤M) (by decide : 3≤5)
  have hw' : r.word.length≤100*(N+1)*M^5 :=
    hw.trans (Nat.mul_le_mul_left (100*(N+1)) hpow)
  have hb := NearCubicGates.Close.CellsPack.lang_le2 StageRecovery.packetCallee
    (bitmapSizes B1 B2 coefficient degree) r.word r.sourceSteps
  change r.budget≤10^6*((r.sourceSteps+1)*
    Gof StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) (leadOnes r.word)^2)+
      10*r.word.length at hb
  change r.budget≤10^15*(N+1)*M^5
  nlinarith only [hb,hm',hw']

/-- `prop:time`, paper/paper.tex: the scalar
mass used in the compiled bitmap bound is supplied by the actual
original source, rather than by an assumed runtime certificate. -/
theorem bitmapBudget_scalar_bound {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) :
    r.budget≤10^15*(paddedCount r.call.n p.1.k+1)*
      (bitmapScalarMass coefficient degree (PreparedScheduleRequest.mk r.call r.witness p hd))^5 :=
  bitmapBudget_of_scalar_bounds r p hd _ (bitmapScalar_bounds r p hd)

/-- `prop:time`, paper/paper.tex: uniformly
over every physically supplied signed native batch, selected bitmap
execution has one native census and only polynomial call-word overhead. -/
theorem bitmapBudget_selected_polynomial (B1 B2 coefficient degree : ℕ) :
    ∃K e : ℕ,∀(r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call),
      Program.dispatch B1 B2 r.call=some p→
      r.budget≤K*(paddedCount r.call.n p.1.k+1)*((callWord r.call).length+1)^e := by
  obtain ⟨K,e,hK⟩ := (bitmapScalarMassPolynomial B1 B2 coefficient degree).pow 5
  refine ⟨10^15*K,e,fun r p hd => ?_⟩
  have hs := bitmapBudget_scalar_bound r p hd
  have hm := hK (PreparedScheduleRequest.mk r.call r.witness p hd)
  have hh := Nat.mul_le_mul_left (10^15*(paddedCount r.call.n p.1.k+1)) hm
  exact hs.trans (hh.trans_eq (by ring))

/-- `sec:params` and `prop:time`, paper/paper.tex: a false preparation executes only the default code;
its exact cold input-copy and compiler costs remain polynomial in the
original call word for every witness. -/
theorem bitmapBudget_default_polynomial (B1 B2 coefficient degree : ℕ) :
    ∃K e : ℕ,∀r : BitmapRequest B1 B2 coefficient degree,
      Program.dispatch B1 B2 r.call=none→
      r.budget≤K*((callWord r.call).length+1)^e := by
  let z := bitmapSizes B1 B2 coefficient degree
  let C0 := 10^6*(11*Gof StageRecovery.packetCallee z 0^2)
  let P := 200*(Cells.ParameterArithmetic.preparationCoefficient B1+5)
  let d := B1+12
  refine ⟨C0+10*(P+3),d,fun r hd => ?_⟩
  have ht : r.tests=[] := by
    apply List.eq_nil_of_length_eq_zero
    rw [r.count_eq,countHeaderValue,hd]
  have hlen : r.word.length=(Program.prepWord B1 B2 r.call r.witness).length+3 := by
    unfold BitmapRequest.word
    rw [ht]
    have hn : (RepairRepresentation.natWord 0).length=3 := by decide
    simp only [List.length_append,List.length_nil,nativeTestStream,List.flatMap_nil,hn,Nat.add_zero]
  obtain ⟨rest,hword⟩ := r.word_default hd
  have hlead : leadOnes r.word=0 := by rw [hword];rfl
  have hl : r.budget≤10^6*((r.sourceSteps+1)*
      Gof StageRecovery.packetCallee z (leadOnes r.word)^2)+10*r.word.length :=
    NearCubicGates.Close.CellsPack.lang_le2 StageRecovery.packetCallee z r.word r.sourceSteps
  have hsource : r.sourceSteps=10 := by unfold BitmapRequest.sourceSteps;rw [hd]
  conv at hl =>
    rhs
    rw [hsource,hlead,hlen]
  have hp := Cells.all_calls_prepWord_length B1 B2 r.call r.witness
  change (Program.prepWord B1 B2 r.call r.witness).length≤P*((callWord r.call).length+1)^d at hp
  have hpow : 1≤((callWord r.call).length+1)^d := Nat.one_le_pow _ _ (by omega)
  change r.budget≤C0+10*((Program.prepWord B1 B2 r.call r.witness).length+3) at hl
  change r.budget≤(C0+10*(P+3))*((callWord r.call).length+1)^d
  nlinarith only [hl,hp,hpow]

end NearQuarticWires.StageCertificateControl
