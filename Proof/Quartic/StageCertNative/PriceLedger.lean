import Proof.Quartic.StageCertNative.PriceOriginal

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: a fixed
original-arity polynomial per original column lies in the first term
of the actual dispatched three-term envelope. -/
theorem OriginalPrice.ledger {B1 B2 : ℕ} {f : IndexedRequest B1 B2→ℕ}
    (h : OriginalPrice f) :
    ∃K E : ℕ,∀r : IndexedRequest B1 B2,
      f r≤K*((callWord r.prepared.call).length+1)^E+
        K*Program.runEnvelope B1 B2 E r.prepared.call := by
  obtain ⟨C,E,h⟩:=h
  refine ⟨C*2^E,E,fun r=>?_⟩
  have hn : 1≤r.prepared.call.n := (zeroMoment r).rules.n_pos
  have hp : (r.prepared.call.n+1)^E≤2^E*r.prepared.call.n^E := by
    exact (Nat.pow_le_pow_left (by omega : r.prepared.call.n+1≤2*r.prepared.call.n) E).trans_eq
      (mul_pow _ _ _)
  have henv : 2^(r.prepared.call.n-r.prepared.selected.1.k)*r.prepared.call.n^E≤
      Program.runEnvelope B1 B2 E r.prepared.call := by
    unfold Program.runEnvelope
    rw [r.prepared.dispatched]
    dsimp only
    have hpower:=Nat.pow_le_pow_right hn
      (show E≤2*r.prepared.selected.1.Jmax+E by omega)
    have hfirst:=Nat.mul_le_mul_left
      (2^(r.prepared.call.n-r.prepared.selected.1.k)) hpower
    unfold Machine.propTimeEnvelope
    have hadd (a b c : ℕ) : a≤a+b+c := by omega
    exact hfirst.trans (hadd _ _ _)
  have hb : f r≤(C*2^E)*Program.runEnvelope B1 B2 E r.prepared.call := by
    calc
      _≤C*(r.prepared.call.n+1)^E*2^(r.prepared.call.n-r.prepared.selected.1.k) := h r
      _≤C*(2^E*r.prepared.call.n^E)*2^(r.prepared.call.n-r.prepared.selected.1.k) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
      _=(C*2^E)*(2^(r.prepared.call.n-r.prepared.selected.1.k)*r.prepared.call.n^E) := by ring
      _≤_ := Nat.mul_le_mul_left _ henv
  omega

end NearQuarticWires.StageCertNative
