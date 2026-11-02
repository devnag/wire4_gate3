import Proof.Quartic.StageLiftTokens.TokenRun
import Proof.Quartic.StageCert.FoldTokens
import Proof.Quartic.StageLift.RegisterFrame

/-!
# Literal Fermat product closure

`lem:residue` and `lem:print`, paper/paper.tex: after all original factors, the source emits one and
exactly `2(J+1)` multiplication tokens. The count is
computed from the retained chain scalar by real bounded operations.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def productCount : St VV MM :=
  .seq (.op (.copy sourceRecordLimit degreeChain))
    (.seq (.op (.inc sourceRecordLimit)) (.op (.shl sourceRecordLimit)))

theorem productCount_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C productCount a 5 (fun b=>
      b.env sourceRecordLimit=2*(r.child.selected.1.J+1) ∧ b.out=a.out ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b [sourceRecordLimit]) := by
  have hh : Hs C productCount a 5 (fun b=>
      b.env sourceRecordLimit=2*(r.child.selected.1.J+1) ∧ b.sh=a.sh ∧
      Cst b ∧ Fr a b [sourceRecordLimit]) := by
    unfold productCount
    refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C sourceRecordLimit degreeChain a (by decide)) ?_
    rintro b rfl
    let b := a.set sourceRecordLimit (a.env degreeChain)
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C sourceRecordLimit b (by
      change a.env degreeChain+1<2^C.Wd
      rw [h.chainCount]
      have hw:=h.target_room
      omega)) ?_
    rintro d rfl
    let d := b.set sourceRecordLimit (b.env sourceRecordLimit+1)
    refine (hs_shl C sourceRecordLimit d (by
      change 2*(a.env degreeChain+1)<2^C.Wd
      rw [h.chainCount]
      have hw:=h.target_room
      omega)).mono le_rfl ?_
    rintro z rfl
    have hf : Fr a (d.set sourceRecordLimit (2*d.env sourceRecordLimit)) [sourceRecordLimit] :=
      (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
    exact ⟨by change 2*(a.env degreeChain+1)=_; rw [h.chainCount],rfl,
      Cst.of_fr h.constants hf (by decide),hf⟩
  obtain ⟨b,n,he,hn,bn,bs,bc,bfr⟩:=hh
  have bsrc:=Same.of_sh bs
  have hf : SourceFrame a b := SourceFrame.of_rest
    (by rw [bsrc.ip,bsrc.ram,bsrc.rc,bsrc.kin,bsrc.kout,bsrc.kc]) bfr (by decide)
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bn,bsrc.out,h.of_frame bc hv hf,hf,bfr⟩

def productCloser : St VV MM :=
  .seq (emitOperator (.const 1)) (.seq productCount (emitCopies .mul))

def productCloserCost (J : ℕ) : ℕ := 40*(J+1)+40

theorem productCloser_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C productCloser a (productCloserCost r.child.selected.1.J) (fun b=>
      b.out=a.out++tokWord (.const 1)++(List.replicate (2*(r.child.selected.1.J+1)) .mul).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ b.env amplifierIndex=a.env amplifierIndex) := by
  have hh : Hs C productCloser a (productCloserCost r.child.selected.1.J) (fun b=>
      b.out=a.out++tokWord (.const 1)++(List.replicate (2*(r.child.selected.1.J+1)) .mul).flatMap tokWord ∧
      SourceFrame a b ∧ Cst b) := by
    unfold productCloser
    apply Hx.hs
    refine Hs.then (emitOperator_ready C r a E h (.const 1))
      (fun b ⟨bo,br,bf,_bfr⟩ n1 hn1=>?_)
    refine Hs.then (productCount_run C r b E br)
      (fun d ⟨dn,doo,dr,df,_dfr⟩ n2 hn2=>?_)
    refine Hs.last (emitCopies_run C .mul d dr.constants (2*(r.child.selected.1.J+1)) dn
      (by have hw:=dr.target_room; omega)) (fun z ⟨zo,zs,zc,zfr⟩ n3 hn3=>?_)
    have zf : SourceFrame d z := SourceFrame.of_rest zs zfr (by decide)
    refine ⟨⟨by rw [zo,doo,bo],bf.trans (df.trans zf),zc⟩,?_⟩
    have h1 : (tokWord (.const 1)).length=9 := by decide
    have hm : (tokWord .mul).length=7 := by decide
    rw [h1] at hn1
    rw [hm] at hn3
    unfold productCloserCost
    omega
  obtain ⟨b,n,he,hn,bo,bf,bc⟩:=hh
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bo,h.of_frame bc hv bf,bf,avoidsRegister_spec he (by decide)⟩

end NearQuarticWires.StageLiftTokens
