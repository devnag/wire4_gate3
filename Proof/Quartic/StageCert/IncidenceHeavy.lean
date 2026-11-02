import Proof.Quartic.StageCert.IncidenceCall

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: the public heavy-coordinate
cutoff is retained separately from all raw gate parser registers. -/
def heavyThreshold : Fin VV := ⟨96,by decide⟩

/-- `def:mask`, paper/paper.tex: one literal heavy-coordinate
flag, computed from the full original occurrence count. -/
def heavyBit : Fin VV := ⟨97,by decide⟩

/-- `def:mask`, paper/paper.tex: the heavy test uses the
inclusive threshold `dstar≤degree`, as in the actual structural mask. -/
def setHeavyFlag : St VV :=
  .ite (.lt censusTotal heavyThreshold) (.op (.zero heavyBit)) (.op (.copy heavyBit v1))

/-- `def:mask`, paper/paper.tex: the physical heavy flag is
exact and changes no raw count, coordinate, cursor or witness byte. -/
theorem setHeavyFlag_run (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C setHeavyFlag a 2 (fun b =>
      b.env heavyBit=bnat (a.env heavyThreshold≤a.env censusTotal) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b [heavyBit]) := by
  unfold setHeavyFlag
  refine Hs.ite (c := .lt censusTotal heavyThreshold) (show censusTotal≠heavyThreshold by decide) ?_ ?_
  · intro he
    have hlt : a.env censusTotal<a.env heavyThreshold := by
      simpa only [Cnd.eval,decide_eq_true_eq] using he
    refine (hs_zero C heavyBit a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [bnat,show ¬a.env heavyThreshold≤a.env censusTotal by omega],rfl,rfl,rfl,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩,Fr.set _ _ (by simp)⟩
  · intro he
    have hge : a.env heavyThreshold≤a.env censusTotal := by
      simpa only [Cnd.eval,decide_eq_false_iff_not,not_lt] using he
    refine (hs_copy C heavyBit v1 a (by decide)).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [bnat,hge,hc.one],rfl,rfl,rfl,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩,Fr.set _ _ (by simp)⟩

/-- `sec:algorithm`, paper/paper.tex: the complete original-call
incidence extraction is followed by its literal structural-mask flag. -/
def readHeavyCoordinate : St VV := .seq readCoordinateCall setHeavyFlag

/-- `sec:algorithm`, paper/paper.tex: the exact numeric incidence
and heavy-coordinate flag are derived from the original public call. -/
theorem readHeavyCoordinate_prefix_run (C : Ctx) (c : Call) (i : Fin c.n) (suffix : List Bool) (a : DS VV)
    (hc : Cst a) (hcp : a.cp=0) (ht : a.env censusTotal=0)
    (hcoord : a.env coordinate=i.val) (hcw : C.cw=callWord c++suffix)
    (hW : 2*C.cw.length+8≤C.Wd) (hL : 2*C.cw.length+4<2^C.Wd) :
    Hs C readHeavyCoordinate a (1201*(C.cw.length+2)^3) (fun b =>
      b.env censusTotal=Cells.incidence (c.first.gates++c.second.gates) i ∧
      b.env heavyBit=bnat (a.env heavyThreshold≤Cells.incidence (c.first.gates++c.second.gates) i) ∧
      b.cp=pos3 c ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      Fr a b (heavyBit::callScratch)) := by
  unfold readHeavyCoordinate
  refine Hx.hs (Hs.then (readCoordinateCall_prefix_run C c i suffix a hc hcp ht hcoord hcw hW hL)
    (fun b ⟨bt,bc,bw,bo,bconst,bf⟩ n1 hn1 => ?_))
  refine Hs.last (setHeavyFlag_run C b bconst)
    (fun d ⟨dh,dc,dw,doo,dconst,df⟩ n2 hn2 => ?_)
  refine ⟨⟨(df _ (by decide)).trans bt,?_,dc.trans bc,dw.trans bw,doo.trans bo,dconst,
    (bf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)).trans
      (df.weaken (by simp))⟩,?_⟩
  · rw [dh,bf heavyThreshold (by decide),bt]
  · have hp : 2^3≤(C.cw.length+2)^3 := Nat.pow_le_pow_left (by omega) 3
    norm_num at hp
    omega

/-- `sec:algorithm`, paper/paper.tex: the prefix-aware physical
heavy-coordinate extractor specializes to the original public call. -/
theorem readHeavyCoordinate_run (C : Ctx) (c : Call) (i : Fin c.n) (a : DS VV)
    (hc : Cst a) (hcp : a.cp=0) (ht : a.env StagePrep.censusTotal=0)
    (hcoord : a.env coordinate=i.val) (hcw : C.cw=callWord c)
    (hW : 2*C.cw.length+8≤C.Wd) (hL : 2*C.cw.length+4<2^C.Wd) :
    Hs C readHeavyCoordinate a (1201*(C.cw.length+2)^3) (fun b =>
      b.env StagePrep.censusTotal=Cells.incidence (c.first.gates++c.second.gates) i ∧
      b.env heavyBit=bnat (a.env heavyThreshold≤Cells.incidence (c.first.gates++c.second.gates) i) ∧
      b.cp=pos3 c ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
      Fr a b (heavyBit::callScratch)) := by
  exact readHeavyCoordinate_prefix_run C c i [] a hc hcp ht hcoord
    (by simpa only [List.append_nil] using hcw) hW hL

end NearQuarticWires.StageCert.Incidence
