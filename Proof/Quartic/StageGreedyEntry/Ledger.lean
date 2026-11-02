import Proof.Quartic.StageGreedyEntry.Stages
import Proof.Quartic.StageGreedyEntry.HeaderBound

/-!
# The selected per-entry ledger

Paper: `lem:print`, `sec:params` and `prop:time`, paper/paper.tex.

Small scalars of one entry (arity, dense width, stack width, modulus bits) are polynomial in the original
arity; every intermediate word is bounded by the clock of the stage that wrote it; the prefix wrapper
is linear; the only square is the per-walk equality-row clock, where the cut stream has at most
`Uocc^D` cuts of polynomial width (`equality_ebb`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5
open StagePrint StageGreedyCollector StageGreedyEntryBounds

variable {B1 B2 : ℕ}

theorem ebb_mul_arity {b : GreedyEntry.Request B1 B2→ℕ} (h : EntryBudgetBound b) (K e : ℕ) :
    EntryBudgetBound (fun r=>K*(r.source.child.call.n+1)^e*b r) := by
  obtain ⟨K',e',hK⟩:=h
  refine ⟨K*K',e+e',fun r=>?_⟩
  calc
    _≤K*(r.source.child.call.n+1)^e*(K'*(r.source.child.call.n+1)^e'*
        (r.source.child.selected.1.Uocc^(2*r.degree)+1)) := Nat.mul_le_mul_left _ (hK r)
    _=_ := by ring

/-- A bound by a fixed arity polynomial gives the selected bound. -/
theorem ebb_of_arity {b : GreedyEntry.Request B1 B2→ℕ} (h : ∃K e : ℕ,∀r,b r≤K*(r.source.child.call.n+1)^e) :
    EntryBudgetBound b := by
  obtain ⟨K,e,hK⟩:=h
  exact ebb_mono (ebb_arity K e) hK

/-- `sec:params`, paper/paper.tex: the original source envelope is polynomial. -/
theorem envelope_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    entryEnvelope r+1≤K*(r.source.child.call.n+1)^e :=
  entryEnvelope_polynomial B1 B2

/-- `lem:print`, paper/paper.tex: the literal entry word meets the selected bound. -/
theorem word_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>(EntryFormat.ofGreedy r).word.length) := by
  obtain ⟨C,E,hC⟩:=envelope_arity B1 B2
  refine ⟨10^27*C^8,8*E,fun r=>?_⟩
  have h2:=word_length_le r
  have h4 : (entryEnvelope r+1)^8≤C^8*(r.source.child.call.n+1)^(8*E) := by
    calc
      _≤(C*(r.source.child.call.n+1)^E)^8 := Nat.pow_le_pow_left (hC r) 8
      _=_ := by ring
  calc
    _≤10^27*(entryEnvelope r+1)^8*(r.source.child.selected.1.Uocc^(2*r.degree)+1) := (Nat.le_succ _).trans h2
    _≤10^27*(C^8*(r.source.child.call.n+1)^(8*E))*(r.source.child.selected.1.Uocc^(2*r.degree)+1) := by gcongr
    _=_ := by ring

/-- `lem:print`, paper/paper.tex: the stack width is polynomial in the original arity. -/
theorem stackWidth_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    r.termRequest.stackWidth+1≤K*(r.source.child.call.n+1)^e := by
  refine ⟨5*(sizingC B1 B2+1)^2,2*sizingE B1 B2,fun r=>?_⟩
  have h1:=hd_stackWidth_le r
  have h2:=sizing_spec r
  obtain ⟨z,hz⟩ : ∃z,z=(EntryFormat.ofGreedy r).sizingMagnitude := ⟨_,rfl⟩
  obtain ⟨P,hP⟩ : ∃P,P=(r.source.child.call.n+1)^sizingE B1 B2 := ⟨_,rfl⟩
  rw [←hz] at h1 h2
  rw [←hP] at h2
  have hP1 : 1≤P := by rw [hP];exact Nat.one_le_pow _ _ (by omega)
  have hz2 : z≤(sizingC B1 B2+1)*P := h2.trans (Nat.mul_le_mul_right _ (by omega))
  have hsq : z^2≤((sizingC B1 B2+1)*P)^2 := Nat.pow_le_pow_left hz2 2
  have hpow : (r.source.child.call.n+1)^(2*sizingE B1 B2)=P^2 := by rw [hP,←pow_mul,Nat.mul_comm]
  rw [hpow]
  have hC1 : 1≤(sizingC B1 B2+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hP2 : P≤P^2 := Nat.le_self_pow (by decide) _
  nlinarith

/-- `sec:params`, paper/paper.tex: the modulus has polynomially many bits. -/
theorem modulusBits_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    natBitLength r.modulus+1≤K*(r.source.child.call.n+1)^e := by
  obtain ⟨C,E,hC⟩:=envelope_arity B1 B2
  refine ⟨C^2+1,2*E,fun r=>?_⟩
  have hq:=(entry_headers r).2.2.2.2.1
  have h2 : (entryEnvelope r+1)^2≤C^2*(r.source.child.call.n+1)^(2*E) := by
    calc
      _≤(C*(r.source.child.call.n+1)^E)^2 := Nat.pow_le_pow_left (hC r) 2
      _=_ := by ring
  have h1 : 1≤(r.source.child.call.n+1)^(2*E) := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The dense width is at most the arity plus one. -/
theorem wd_le (r : GreedyEntry.Request B1 B2) : wd r≤r.source.child.call.n+1 := by
  unfold wd;omega

theorem natWord_length_le' (v : ℕ) : (natWord v).length≤2*v+3 :=
  NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le_self v

/-- `prop:time`, paper/paper.tex: the cold prefix wrapper is linear. -/
theorem ebb_prefix {t : GreedyEntry.Request B1 B2→ℕ} {L b : GreedyEntry.Request B1 B2→ℕ}
    (ht : EntryBudgetBound (fun r=>(natWord (t r)).length)) (hL : EntryBudgetBound L)
    (hb : EntryBudgetBound b) :
    EntryBudgetBound (fun r=>StageCertificateControl.nativePrefixBudget (t r) (L r) (b r)) :=
  ebb_mono (ebb_smul (ebb_add (ebb_add (ebb_add ht hL) hb) (ebb_const 1)) 20002)
    (fun r=>StageCertificateControl.nativePrefixBudget_linear (t r) (L r) (b r))

/-- `prop:time`, paper/paper.tex: a framed reply is shorter than its clock. -/
theorem framed_length_le {Request : Type} {input middle : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (middle r)) budget) (r : Request) :
    (middle r).length≤budget r := by
  have h:=Control.output_length_le f r
  simp only [frame_length] at h
  omega

theorem natWord_wd_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>(natWord (wd r)).length) :=
  ebb_mono (ebb_arity 5 1) (fun r=>by
    have h1:=natWord_length_le' (wd r)
    have h2:=wd_le r
    simp only [pow_one]
    omega)

theorem natWord_modulus_ebb (B1 B2 : ℕ) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>(natWord r.modulus).length) :=
  ebb_mono (word_ebb B1 B2) (fun r=>by
    have h:=congrArg List.length (word_fields (EntryFormat.ofGreedy r))
    simp only [List.length_append] at h
    change (natWord (EntryFormat.ofGreedy r).scale).length≤_
    omega)

theorem natWord_stack_ebb (B1 B2 : ℕ) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>(natWord r.termRequest.stackWidth).length) := by
  obtain ⟨K,e,hK⟩:=stackWidth_arity B1 B2
  exact ebb_mono (ebb_arity (2*K+3) e) (fun r=>by
    have h1:=natWord_length_le' r.termRequest.stackWidth
    have h2:=hK r
    have h3 : 1≤(r.source.child.call.n+1)^e := Nat.one_le_pow _ _ (by omega)
    nlinarith)

/-- The small widths of one entry are polynomial in the original arity. -/
theorem scale_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    wd r+r.termRequest.stackWidth+natBitLength r.modulus+2≤K*(r.source.child.call.n+1)^e := by
  obtain ⟨K1,e1,h1⟩:=stackWidth_arity B1 B2
  obtain ⟨K2,e2,h2⟩:=modulusBits_arity B1 B2
  refine ⟨K1+K2+2,e1+e2+1,fun r=>?_⟩
  have hw:=wd_le r
  have a1 : (r.source.child.call.n+1)^e1≤(r.source.child.call.n+1)^(e1+e2+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have a2 : (r.source.child.call.n+1)^e2≤(r.source.child.call.n+1)^(e1+e2+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have a3 : (r.source.child.call.n+1)^1≤(r.source.child.call.n+1)^(e1+e2+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have b1:=h1 r
  have b2:=h2 r
  have c1:=Nat.mul_le_mul_left K1 a1
  have c2:=Nat.mul_le_mul_left K2 a2
  rw [pow_one] at a3
  nlinarith

/-- The literal length of a cut list with dense vectors of a common width. -/
theorem cutStream_length (p width : ℕ) (cuts : List MatrixScoreBatch.Cut)
    (h : ∀c∈cuts,c.leftWeights.length=width ∧ c.rightWeights.length=width) :
    (cuts.flatMap (MatrixScoreBatch.cutWord p)).length=cuts.length*((2*width+2)*(2*p+3)) := by
  induction cuts with
  | nil => simp
  | cons c cs ih =>
    have hc:=h c (by simp)
    have ih':=ih (fun d hd=>h d (by simp [hd]))
    simp only [List.flatMap_cons,List.length_append,ih',List.length_cons,
      StageModularCuts.cutWord_length,hc.1,hc.2]
    ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the per-walk
equality-row clock is the only square, of a stream of at most `Uocc^D` cuts. -/
theorem equality_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
    10^30*(PrimT.C4Geo.width (equalityRequest r).parameters+(equalityRequest r).fieldWidth+2)^20*
      (((equalityRequest r).cuts.flatMap (MatrixScoreBatch.cutWord (equalityRequest r).fieldWidth)).length+1)^2) := by
  obtain ⟨K,e,hK⟩:=scale_arity B1 B2
  refine ⟨10^30*64*K^24,24*e,fun r=>?_⟩
  have hlen:=cutStream_length (equalityRequest r).fieldWidth _ (equalityRequest r).cuts (equalityRequest r).lengths
  have hcount : (equalityRequest r).cuts.length≤r.source.child.selected.1.Uocc^r.degree := entry_cuts_count r
  have hT:=hK r
  have hw : PrimT.C4Geo.width (equalityRequest r).parameters=wd r := wd_eq r
  have hf : (equalityRequest r).fieldWidth=r.termRequest.stackWidth := rfl
  beta_reduce
  rw [hlen,hw,hf]
  obtain ⟨V,hV⟩ : ∃V,V=r.source.child.selected.1.Uocc^r.degree := ⟨_,rfl⟩
  have hU : r.source.child.selected.1.Uocc^(2*r.degree)=V^2 := by rw [hV,←pow_mul,Nat.mul_comm]
  rw [hU]
  rw [←hV] at hcount
  obtain ⟨c,hc⟩ : ∃c,c=(equalityRequest r).cuts.length := ⟨_,rfl⟩
  rw [←hc] at hcount ⊢
  obtain ⟨S,hS⟩ : ∃S,S=wd r+r.termRequest.stackWidth+2 := ⟨_,rfl⟩
  have hS2 : 2≤S := by omega
  have hST : S≤K*(r.source.child.call.n+1)^e := by omega
  have hM : (2*wd r+2)*(2*r.termRequest.stackWidth+3)≤4*S^2 := by
    have:=Nat.mul_le_mul (show 2*wd r+2≤2*S by omega) (show 2*r.termRequest.stackWidth+3≤2*S by omega)
    nlinarith
  rw [←hS]
  obtain ⟨M,hMd⟩ : ∃M,M=(2*wd r+2)*(2*r.termRequest.stackWidth+3) := ⟨_,rfl⟩
  rw [←hMd] at hM ⊢
  have h1 : c*M+1≤(V+1)*(M+1) := by nlinarith
  have h2 : (c*M+1)^2≤(V+1)^2*(M+1)^2 := by rw [←mul_pow];exact Nat.pow_le_pow_left h1 2
  have h3 : (V+1)^2≤2*(V^2+1) := by nlinarith
  have h4 : (M+1)^2≤25*S^4 := by
    have h : M+1≤5*S^2 := by nlinarith
    calc
      (M+1)^2≤(5*S^2)^2 := Nat.pow_le_pow_left h 2
      _=25*S^4 := by ring
  have h5 : S^24≤K^24*(r.source.child.call.n+1)^(24*e) := by
    calc
      S^24≤(K*(r.source.child.call.n+1)^e)^24 := Nat.pow_le_pow_left hST 24
      _=_ := by ring
  calc
    10^30*S^20*(c*M+1)^2≤10^30*S^20*((V+1)^2*(M+1)^2) := by gcongr
    _≤10^30*S^20*((2*(V^2+1))*(25*S^4)) := by gcongr
    _=10^30*50*S^24*(V^2+1) := by ring
    _≤10^30*64*(K^24*(r.source.child.call.n+1)^(24*e))*(V^2+1) := by gcongr;norm_num
    _=_ := by ring

end NearQuarticWires.StageGreedyEntry
