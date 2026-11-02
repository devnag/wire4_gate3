import Proof.Quartic.StageCertNative.EntryScale
import Proof.Quartic.StageCert.MomentSourcePrice

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires
open StageCert.Tokens

/-- `prop:time`, paper/paper.tex: a fixed
original-arity polynomial times the selected occurrence census raised
to a fixed multiple of the actual complete moment degree. -/
def JobPrice {B1 B2 : ℕ} (f : TermJob B1 B2→ℕ) (d : ℕ) : Prop :=
  ∃C E : ℕ,∀r,f r≤C*(r.moment.call.n+1)^E*
    r.moment.selected.1.Uocc^(d*r.moment.packet.degree)

theorem job_occurrence_pos {B1 B2 : ℕ} (r : TermJob B1 B2) :
    1≤r.moment.selected.1.Uocc := by
  rw [r.moment.rules.Uocc_eq]
  omega

theorem job_dimension_pos {B1 B2 : ℕ} (r : TermJob B1 B2) : 1≤r.moment.selected.1.k := by
  by_contra h
  have hk : r.moment.selected.1.k=0 := by omega
  have hh:=Cells.ParameterRules.N_ge_two r.moment.rules
  rw [r.moment.rules.N_eq,hk] at hh
  norm_num at hh

theorem job_degree_ge_eight {B1 B2 : ℕ} (r : TermJob B1 B2) : 8≤r.moment.packet.degree := by
  have hk:=job_dimension_pos r
  change 8≤16*r.moment.selected.1.Xmax+8*r.moment.selected.1.k
  omega

theorem JobPrice.of_arity {B1 B2 : ℕ} {f : TermJob B1 B2→ℕ}
    (h : ∃C E:ℕ,∀r,f r≤C*(r.moment.call.n+1)^E) : JobPrice f 0 := by
  simpa only [JobPrice,zero_mul,pow_zero,mul_one] using h

theorem JobPrice.constant {B1 B2 : ℕ} (c : ℕ) : JobPrice (fun _ : TermJob B1 B2=>c) 0 := by
  exact JobPrice.of_arity ⟨c,0,by intro r;simp⟩

theorem JobPrice.mono {B1 B2 : ℕ} {f g : TermJob B1 B2→ℕ} {d : ℕ}
    (hg : JobPrice g d) (hfg : ∀r,f r≤g r) : JobPrice f d := by
  obtain ⟨C,E,h⟩:=hg
  exact ⟨C,E,fun r=>(hfg r).trans (h r)⟩

theorem JobPrice.raise {B1 B2 : ℕ} {f : TermJob B1 B2→ℕ} {d e : ℕ}
    (h : JobPrice f d) (he : d≤e) : JobPrice f e := by
  obtain ⟨C,E,h⟩:=h
  refine ⟨C,E,fun r=>(h r).trans ?_⟩
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (job_occurrence_pos r)
    (Nat.mul_le_mul_right _ he))

theorem JobPrice.add {B1 B2 : ℕ} {f g : TermJob B1 B2→ℕ} {d : ℕ}
    (hf : JobPrice f d) (hg : JobPrice g d) : JobPrice (fun r=>f r+g r) d := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C+K,E+L,fun r=>?_⟩
  have he : (r.moment.call.n+1)^E≤(r.moment.call.n+1)^(E+L) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hl : (r.moment.call.n+1)^L≤(r.moment.call.n+1)^(E+L) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _≤C*(r.moment.call.n+1)^E*r.moment.selected.1.Uocc^(d*r.moment.packet.degree)+
       K*(r.moment.call.n+1)^L*r.moment.selected.1.Uocc^(d*r.moment.packet.degree) :=
      Nat.add_le_add (hf r) (hg r)
    _≤C*(r.moment.call.n+1)^(E+L)*r.moment.selected.1.Uocc^(d*r.moment.packet.degree)+
       K*(r.moment.call.n+1)^(E+L)*r.moment.selected.1.Uocc^(d*r.moment.packet.degree) := by
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he))
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hl))
    _=_ := by ring

theorem JobPrice.mul {B1 B2 : ℕ} {f g : TermJob B1 B2→ℕ} {d e : ℕ}
    (hf : JobPrice f d) (hg : JobPrice g e) : JobPrice (fun r=>f r*g r) (d+e) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C*K,E+L,fun r=>?_⟩
  calc
    _≤(C*(r.moment.call.n+1)^E*r.moment.selected.1.Uocc^(d*r.moment.packet.degree))*
      (K*(r.moment.call.n+1)^L*r.moment.selected.1.Uocc^(e*r.moment.packet.degree)) :=
      Nat.mul_le_mul (hf r) (hg r)
    _=_ := by rw [pow_add,add_mul,pow_add];ring

theorem JobPrice.pow {B1 B2 : ℕ} {f : TermJob B1 B2→ℕ} {d : ℕ}
    (hf : JobPrice f d) (p : ℕ) : JobPrice (fun r=>f r^p) (d*p) := by
  obtain ⟨C,E,hf⟩:=hf
  refine ⟨C^p,E*p,fun r=>?_⟩
  calc
    _≤(C*(r.moment.call.n+1)^E*r.moment.selected.1.Uocc^(d*r.moment.packet.degree))^p :=
      Nat.pow_le_pow_left (hf r) _
    _=_ := by
      rw [mul_pow,mul_pow,←pow_mul,←pow_mul]
      congr 2
      ring

theorem price_runtimeScale (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.runtimeScale) 0 :=
  JobPrice.of_arity ⟨momentRuntimeCoefficient B1 B2,momentRuntimeExponent B1 B2,
    fun r=>r.moment.runtimeScale_arity⟩

theorem price_wordLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.word.length) 0 :=
  JobPrice.of_arity ⟨sharedSourceCoefficient B1 B2,sharedSourceExponent B1 B2,
    fun r=>(by have hh:=nFirstWord_length_arity r
               unfold nFirstWord at hh
               rw [List.length_append] at hh
               omega)⟩

theorem price_degree (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.packet.degree) 0 :=
  JobPrice.of_arity ⟨1,1,fun r=>(r.degree_le_arity.trans (by simp))⟩

end NearQuarticWires.StageCertNative
