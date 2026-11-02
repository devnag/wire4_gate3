import Proof.Quartic.StageCert.IncidenceStep

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces

/-- `sec:algorithm`, paper/paper.tex: numeric original-coordinate
records are emitted in increasing coordinate order. -/
def incidencePrefix (c : Call) (dstar count : ℕ) : List Bool :=
  (List.range count).flatMap (fun j =>
    if hj : j<c.n then coordinateRecord c dstar ⟨j,hj⟩ else [])

/-- `sec:algorithm`, paper/paper.tex: one further valid original
coordinate appends its exact incidence/heavy record. -/
theorem incidencePrefix_succ (c : Call) (dstar k : ℕ) (hk : k<c.n) :
    incidencePrefix c dstar (k+1)=incidencePrefix c dstar k++coordinateRecord c dstar ⟨k,hk⟩ := by
  simp [incidencePrefix,List.range_succ,List.flatMap_append,hk]

/-- `sec:algorithm`, paper/paper.tex: the complete original
coordinate list is traversed exactly once, independently of all witness bits. -/
def incidenceStream : St VV := .loop (.lt coordinate arity) coordinateStep

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the physical original-source coordinate loop emits the entire
incidence/heavy list with a polynomial binary cost. -/
theorem incidenceStream_run (C : Ctx) (c : Call) (suffix : List Bool) (a : DS VV)
    (hc : Cst a) (hi : a.env coordinate=0) (hn : a.env arity=c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hfit : c.n<2^C.Wd) :
    Hs C incidenceStream a (c.n*(2000*(C.cw.length+2)^3+2)+2) (fun b =>
      b.out=a.out++incidencePrefix c (a.env heavyThreshold) c.n ∧
      b.env coordinate=c.n ∧ b.env arity=c.n ∧ b.env heavyThreshold=a.env heavyThreshold ∧
      b.wq=a.wq ∧ Cst b ∧ Fr a b stepScratch) := by
  let I : ℕ→DS VV→Prop := fun k b =>
    b.env coordinate=k ∧ b.env arity=c.n ∧ b.env heavyThreshold=a.env heavyThreshold ∧
    b.wq=a.wq ∧ b.out=a.out++incidencePrefix c (a.env heavyThreshold) k ∧ Cst b ∧ Fr a b stepScratch
  have hstep : ∀k<c.n,∀b,I k b→
      Cnd.eval b (.lt coordinate arity)=true ∧
      Hs C coordinateStep b (2000*(C.cw.length+2)^3) (I (k+1)) := by
    intro k hk b ⟨bi,bn,bh,bw,bo,bc,bf⟩
    refine ⟨by simp [Cnd.eval,bi,bn,hk],?_⟩
    refine (coordinateStep_run C c suffix ⟨k,hk⟩ b bc bi hcw hW hL hfit).mono le_rfl ?_
    rintro d ⟨doo,di,dw,dc,df⟩
    refine ⟨di,(df _ (by decide)).trans bn,(df _ (by decide)).trans bh,
      dw.trans bw,?_,dc,bf.trans df⟩
    rw [doo,bo,bh,incidencePrefix_succ c (a.env heavyThreshold) k hk,List.append_assoc]
  have hstop : ∀b,I c.n b→Cnd.eval b (.lt coordinate arity)=false := by
    rintro b ⟨bi,bn,_⟩
    simp [Cnd.eval,bi,bn]
  have h := Hs.loopN (C := C) (c := .lt coordinate arity) (s := coordinateStep)
    (show coordinate≠arity by decide) I c.n (2000*(C.cw.length+2)^3) hstep hstop a
    ⟨hi,hn,rfl,rfl,by simp [incidencePrefix],hc,Fr.refl _ _⟩
  refine h.mono le_rfl ?_
  rintro b ⟨bi,bn,bh,bw,bo,bc,bf⟩
  exact ⟨bo,bi,bn,bh,bw,bc,bf⟩

end NearQuarticWires.StageCert.Incidence
