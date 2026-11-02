import Proof.Quartic.StageCertNative.PriceHeader
import Proof.Quartic.StageCertNative.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: one fixed
original-arity polynomial per actual original outer column. -/
def OriginalPrice {B1 B2 : ℕ} (f : IndexedRequest B1 B2→ℕ) : Prop :=
  ∃C E : ℕ,∀r,f r≤C*(r.prepared.call.n+1)^E*
    2^(r.prepared.call.n-r.prepared.selected.1.k)

theorem OriginalPrice.of_job_zero {B1 B2 : ℕ} {f : IndexedRequest B1 B2→ℕ}
    (h : JobPrice (fun r=>f r.base) 0) : OriginalPrice f := by
  obtain ⟨C,E,h⟩:=h
  refine ⟨C,E,fun r=>?_⟩
  have hh:=h (firstJob r)
  simp only [zero_mul,pow_zero,mul_one] at hh
  exact hh.trans (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)

theorem OriginalPrice.constant {B1 B2 : ℕ} (c : ℕ) :
    OriginalPrice (fun _ : IndexedRequest B1 B2=>c) :=
  OriginalPrice.of_job_zero (JobPrice.constant c)

theorem OriginalPrice.mono {B1 B2 : ℕ} {f g : IndexedRequest B1 B2→ℕ}
    (h : OriginalPrice g) (hfg : ∀r,f r≤g r) : OriginalPrice f := by
  obtain ⟨C,E,h⟩:=h
  exact ⟨C,E,fun r=>(hfg r).trans (h r)⟩

theorem OriginalPrice.add {B1 B2 : ℕ} {f g : IndexedRequest B1 B2→ℕ}
    (hf : OriginalPrice f) (hg : OriginalPrice g) : OriginalPrice (fun r=>f r+g r) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C+K,E+L,fun r=>?_⟩
  have he:=Nat.pow_le_pow_right (show 1≤r.prepared.call.n+1 by omega) (show E≤E+L by omega)
  have hl:=Nat.pow_le_pow_right (show 1≤r.prepared.call.n+1 by omega) (show L≤E+L by omega)
  calc
    _≤C*(r.prepared.call.n+1)^E*2^(r.prepared.call.n-r.prepared.selected.1.k)+
        K*(r.prepared.call.n+1)^L*2^(r.prepared.call.n-r.prepared.selected.1.k) :=
      Nat.add_le_add (hf r) (hg r)
    _≤C*(r.prepared.call.n+1)^(E+L)*2^(r.prepared.call.n-r.prepared.selected.1.k)+
        K*(r.prepared.call.n+1)^(E+L)*2^(r.prepared.call.n-r.prepared.selected.1.k) := by
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he))
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hl))
    _=_ := by ring

theorem OriginalPrice.mul_arity {B1 B2 : ℕ} {f g : IndexedRequest B1 B2→ℕ}
    (hf : OriginalPrice f) (hg : JobPrice (fun r=>g r.base) 0) :
    OriginalPrice (fun r=>f r*g r) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C*K,E+L,fun r=>?_⟩
  have hh:=hg (firstJob r)
  simp only [zero_mul,pow_zero,mul_one] at hh
  calc
    _≤(C*(r.prepared.call.n+1)^E*2^(r.prepared.call.n-r.prepared.selected.1.k))*
        (K*(r.prepared.call.n+1)^L) := Nat.mul_le_mul (hf r) hh
    _=_ := by rw [pow_add];ring

end NearQuarticWires.StageCertNative
