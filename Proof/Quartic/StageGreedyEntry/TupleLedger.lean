import Proof.Quartic.StageGreedyEntry.EntryBound
import Proof.Quartic.StagePrintTuple.SetupContract

/-!
# The tuple clock at actual entries

Paper: `lem:print`, `sec:params` and `prop:time`, paper/paper.tex.

A request-level tuple clock of the additive form
`C · small^E · ((1 + V·mc)^(2D) + |termsWord| + 1)`, with `V = 17·|gates|`, a small scale polynomial in the
original arity at actual entries and a child bound `mc ≤ childCap`, meets the selected per-entry bound
(`tuple_ebb_of_ledger`): `1 + V·childCap ≤ Uocc` and the Terms bytes lie inside the literal entry word.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StagePrint StageGreedyCollector

variable {B1 B2 : ℕ}

/-- `sec:params`, paper/paper.tex: the occurrence factor dominates the weighted child base. -/
theorem childBase_le_Uocc (r : GreedyEntry.Request B1 B2) :
    1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap≤
      r.source.child.selected.1.Uocc := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hg : (Builder.allGates r.source.child.call).length≤2*r.source.child.call.n^4 := by
    have hh:=hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
    simpa only [Builder.callInput,Builder.allGates,List.length_append] using hh
  rw [hs.Uocc_eq,hs.NatAtoms_eq,hs.m_eq]
  change 1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap≤
    1+17*(2*r.source.child.call.n^4)*r.source.child.selected.1.childCap
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)) 1

/-- `sec:params`, paper/paper.tex: every original child pool of an actual entry has at
most `childCap` members. -/
theorem nativeKids_le_childCap (r : GreedyEntry.Request B1 B2) (j : Fin (17*(Builder.allGates r.source.child.call).length)) :
    (r.termRequest.toRowContext.nativeKids j).length≤r.source.child.selected.1.childCap := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  rw [hs.childCap_eq]
  exact r.rowContext.nativeKids_length_le j hs.n_pos

/-- `lem:print`, paper/paper.tex: the Terms bytes lie inside the literal entry word. -/
theorem termsBytes_ebb (B1 B2 : ℕ) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>(termsWord r.terms).length) :=
  ebb_mono (word_ebb B1 B2) (fun r=>by
    have h:=congrArg List.length (word_fields (EntryFormat.ofGreedy r))
    simp only [List.length_append,frame_length] at h
    change (termsWord (EntryFormat.ofGreedy r).terms).length≤_
    omega)

/-- `lem:print` and `prop:time`, paper/paper.tex: an additive
request-level tuple clock gives the selected per-entry bound at actual entries. -/
theorem tuple_ebb_of_ledger {tb : StageTuple.TermCutRequest→ℕ} (C E : ℕ)
    (small mc : StageTuple.TermCutRequest→ℕ)
    (hledger : ∀t,tb t≤C*small t^E*((1+17*(Builder.allGates t.header.call).length*mc t)^(2*t.degree)+
      (termsWord t.terms).length+1))
    (hsmall : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,small r.termRequest≤K*(r.source.child.call.n+1)^e)
    (hmc : ∀r : GreedyEntry.Request B1 B2,mc r.termRequest≤r.source.child.selected.1.childCap) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest) := by
  obtain ⟨K,e,hK⟩:=hsmall
  have hU : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
      (1+17*(Builder.allGates r.source.child.call).length*mc r.termRequest)^(2*r.degree)) := by
    refine ⟨1,0,fun r=>?_⟩
    have h1 : 1+17*(Builder.allGates r.source.child.call).length*mc r.termRequest≤
        r.source.child.selected.1.Uocc :=
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hmc r)) 1).trans (childBase_le_Uocc r)
    have h2:=Nat.pow_le_pow_left h1 (2*r.degree)
    simp only [pow_zero,Nat.one_mul]
    omega
  have hsum:=ebb_add (ebb_add hU (termsBytes_ebb B1 B2)) (ebb_const 1)
  refine ebb_mono (ebb_mul_arity hsum (C*K^E) (e*E)) (fun r=>?_)
  have hl:=hledger r.termRequest
  have hs : small r.termRequest^E≤K^E*(r.source.child.call.n+1)^(e*E) := by
    calc
      _≤(K*(r.source.child.call.n+1)^e)^E := Nat.pow_le_pow_left (hK r) E
      _=_ := by ring
  calc
    tb r.termRequest≤C*small r.termRequest^E*((1+17*(Builder.allGates r.source.child.call).length*
        mc r.termRequest)^(2*r.degree)+(termsWord r.terms).length+1) := hl
    _≤C*(K^E*(r.source.child.call.n+1)^(e*E))*((1+17*(Builder.allGates r.source.child.call).length*
        mc r.termRequest)^(2*r.degree)+(termsWord r.terms).length+1) := by gcongr
    _=_ := by ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the tuple clock at
actual entries, from the additive request-level ledger with a child bound `mc` and its precondition,
instantiated at `mc = childCap`. -/
theorem tuple_ebb {tb : StageTuple.TermCutRequest→ℕ} (C E : ℕ)
    (small : StageTuple.TermCutRequest→ℕ→ℕ) (ok : StageTuple.TermCutRequest→ℕ→Prop)
    (hledger : ∀t mc,ok t mc→tb t≤C*small t mc^E*((1+17*(Builder.allGates t.header.call).length*mc)^(2*t.degree)+
      (termsWord t.terms).length+1))
    (hok : ∀r : GreedyEntry.Request B1 B2,ok r.termRequest r.source.child.selected.1.childCap)
    (hsmall : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
      small r.termRequest r.source.child.selected.1.childCap≤K*(r.source.child.call.n+1)^e) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest) := by
  obtain ⟨K,e,hK⟩:=hsmall
  have hU : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
      (1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap)^(2*r.degree)) := by
    refine ⟨1,0,fun r=>?_⟩
    have h2:=Nat.pow_le_pow_left (childBase_le_Uocc r) (2*r.degree)
    simp only [pow_zero,Nat.one_mul]
    omega
  have hsum:=ebb_add (ebb_add hU (termsBytes_ebb B1 B2)) (ebb_const 1)
  refine ebb_mono (ebb_mul_arity hsum (C*K^E) (e*E)) (fun r=>?_)
  have hl:=hledger r.termRequest r.source.child.selected.1.childCap (hok r)
  have hs : small r.termRequest r.source.child.selected.1.childCap^E≤K^E*(r.source.child.call.n+1)^(e*E) := by
    calc
      _≤(K*(r.source.child.call.n+1)^e)^E := Nat.pow_le_pow_left (hK r) E
      _=_ := by ring
  calc
    tb r.termRequest≤C*small r.termRequest r.source.child.selected.1.childCap^E*
        ((1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap)^(2*r.degree)+
          (termsWord r.terms).length+1) := hl
    _≤C*(K^E*(r.source.child.call.n+1)^(e*E))*
        ((1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap)^(2*r.degree)+
          (termsWord r.terms).length+1) := by gcongr
    _=_ := by ring

/-- `sec:params`, paper/paper.tex: the child bound is polynomial in the original arity. -/
theorem childCap_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    r.source.child.selected.1.childCap≤K*(r.source.child.call.n+1)^e := by
  refine ⟨10,3,fun r=>?_⟩
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  rw [hs.childCap_eq]
  change Cells.childCap r.source.child.call.n (NearCubicGates.Close.Counter.B0 r.source.child.call.n)≤_
  unfold Cells.childCap NearCubicGates.Close.Counter.B0
  have h1:=NearCubicGates.Close.Counter.clog_le_self (r.source.child.call.n+1)
  have h2:=NearCubicGates.Close.Counter.clog_le_self r.source.child.call.n
  obtain ⟨n,hn⟩ : ∃n,n=r.source.child.call.n := ⟨_,rfl⟩
  rw [←hn] at h1 h2 ⊢
  have a1 : n*Nat.clog 2 (n+1)≤n*(n+1) := Nat.mul_le_mul_left _ h1
  have a2 : 4*n*Nat.clog 2 (n+1)≤4*(n*(n+1)) := by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ a1
  have a3 : n*(4*n*Nat.clog 2 (n+1)+Nat.clog 2 n+3)≤n*(4*(n*(n+1))+n+3) :=
    Nat.mul_le_mul_left _ (by omega)
  refine a3.trans ?_
  have e1 : n*(4*(n*(n+1))+n+3)=4*n^3+5*n^2+3*n := by ring
  have e2 : 10*(n+1)^3=10*n^3+30*n^2+30*n+10 := by ring
  rw [e1,e2]
  omega

/-- `prop:time`, paper/paper.tex: the structural tuple magnitude at an actual entry,
with the child bound `childCap`, is polynomial in the original arity. It contains no Terms byte. -/
theorem structural_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    r.termRequest.setupStructuralMagnitude+r.termRequest.rowDimension+r.degree+
      17*(Builder.allGates r.source.child.call).length+r.source.child.selected.1.childCap+1≤
        K*(r.source.child.call.n+1)^e := by
  obtain ⟨C,E,hC⟩:=envelope_arity B1 B2
  obtain ⟨K1,e1,h1⟩:=stackWidth_arity B1 B2
  obtain ⟨K2,e2,h2⟩:=childCap_arity B1 B2
  refine ⟨10^27*C^8+K1+K2+100,8*E+e1+e2+1,fun r=>?_⟩
  obtain ⟨hE2,hn,hg,hd,hq,hi⟩:=StageGreedyEntryBounds.entry_headers r
  have hctx:=StageGreedyEntryBounds.context_length r
  have hctxw:=congrArg List.length (contextWord_frames (EntryFormat.ofGreedy r))
  simp only [ctxFields,List.flatMap_cons,List.flatMap_nil,List.length_append,frame_length,
    List.append_nil,List.length_nil] at hctxw
  have hcw : r.termRequest.contextWord.length=(EntryFormat.ofGreedy r).countsWord.length+
      (natWord r.index.val).length := by
    simp only [StageTuple.TermCutRequest.contextWord,EntryFormat.Request.countsWord,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.length_append,Nat.add_assoc]
    rfl
  have hwalk:=NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le hi
  have hdeg:=natWord_length_le' r.degree
  have hwd : r.termRequest.rowDimension=2*wd r := by
    show 2*NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.rowContext.header.prepared.starParams=2*wd r
    rw [wd_eq]
  have hwd2:=wd_le r
  obtain ⟨S,hS⟩ : ∃S,S=StageGreedyEntryBounds.entryEnvelope r+1 := ⟨_,rfl⟩
  obtain ⟨P,hP⟩ : ∃P,P=(r.source.child.call.n+1)^(8*E+e1+e2+1) := ⟨_,rfl⟩
  have hSC : S^8≤C^8*(r.source.child.call.n+1)^(8*E) := by
    rw [hS]
    calc
      _≤(C*(r.source.child.call.n+1)^E)^8 := Nat.pow_le_pow_left (hC r) 8
      _=_ := by ring
  have hn1 : 1≤r.source.child.call.n+1 := by omega
  have p0 : (r.source.child.call.n+1)^(8*E)≤P := by rw [hP];exact Nat.pow_le_pow_right hn1 (by omega)
  have p1 : (r.source.child.call.n+1)^e1≤P := by rw [hP];exact Nat.pow_le_pow_right hn1 (by omega)
  have p2 : (r.source.child.call.n+1)^e2≤P := by rw [hP];exact Nat.pow_le_pow_right hn1 (by omega)
  have p3 : r.source.child.call.n+1≤P := by
    rw [hP];calc
      r.source.child.call.n+1=(r.source.child.call.n+1)^1 := (pow_one _).symm
      _≤_ := Nat.pow_le_pow_right hn1 (by omega)
  have q0 : C^8*(r.source.child.call.n+1)^(8*E)≤C^8*P := Nat.mul_le_mul_left _ p0
  have q1 : K1*(r.source.child.call.n+1)^e1≤K1*P := Nat.mul_le_mul_left _ p1
  have q2 : K2*(r.source.child.call.n+1)^e2≤K2*P := Nat.mul_le_mul_left _ p2
  have hS1 : S≤S^8 := Nat.le_self_pow (by decide) _
  have hW:=h1 r
  have hcc:=h2 r
  have hfin : (10^27*C^8+K1+K2+100)*(r.source.child.call.n+1)^(8*E+e1+e2+1)=
      10^27*(C^8*P)+K1*P+K2*P+100*P := by rw [←hP];ring
  rw [hfin]
  unfold StageTuple.TermCutRequest.setupStructuralMagnitude
  rw [hcw,hwd]
  change r.source.child.call.n+r.termRequest.stackWidth+(callWord r.source.child.call).length+
    ((StagePrint.Header.baseHeaderValues (EntryFormat.ofGreedy r).header).flatMap natWord).length+
    ((EntryFormat.ofGreedy r).countsWord.length+(natWord r.index.val).length)+(natWord r.degree).length+10+
    2*wd r+r.degree+17*(Builder.allGates r.source.child.call).length+r.source.child.selected.1.childCap+1≤_
  change _=2*(2*(callWord r.source.child.call).length+1)+1+_ at hctxw
  rw [←hS] at hctx
  generalize C^8*(r.source.child.call.n+1)^(8*E)=Q at hSC q0
  generalize C^8*P=R at q0 ⊢
  generalize S^8=S8 at hSC hS1 hctx
  generalize K1*(r.source.child.call.n+1)^e1=X1 at hW q1
  generalize K2*(r.source.child.call.n+1)^e2=X2 at hcc q2
  omega

end NearQuarticWires.StageGreedyEntry
