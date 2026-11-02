import Proof.Quartic.StageCarrierEnvelope.Data
import Proof.Quartic.StagePrint.BaseHeader
import Proof.Quartic.StageGamma.BinaryPower
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePrint.Header

/-- `imp:partition` and `lem:print`, paper/paper.tex: retained small binary geometry registers. -/
def droppedVar : Fin VV:=70
def freeVar : Fin VV:=71
def columnVar : Fin VV:=72
def powerIndex : Fin VV:=73

/-- `imp:partition`, paper/paper.tex: compute
free center bits from the actual original n, r and s, using k=r*s. -/
def computeFree : St VV MM :=
  .seq (.op (.mul blockCount syndromeWidth droppedVar))
    (.seq (.op (.copy freeVar arity)) (.op (.sub freeVar droppedVar)))

/-- `imp:partition` and `prop:time`, paper/paper.tex: every arithmetic step uses the physically
read original geometry; no column count or decoded geometry is supplied. -/
theorem computeFree_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a)
    (hn : a.env arity=r.child.call.n) (hr : a.env blockCount=r.child.selected.1.r)
    (hs : a.env syndromeWidth=r.child.selected.1.s) (hW : r.child.call.n<2^C.Wd) :
    Hs C computeFree a 5 (fun b=>
      b.env freeVar=r.child.call.n-r.child.selected.1.k ∧ Same a b ∧ Cst b) := by
  have rules:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hk : r.child.selected.1.r*r.child.selected.1.s≤r.child.call.n := by
    rw [←rules.k_eq]
    exact rules.k_lt_n.le
  unfold computeFree
  refine Hs.seq (t2:=3) (hs_mul C blockCount syndromeWidth droppedVar a
    (by decide) (by decide) (by decide) (by rw [hr,hs];omega)) ?_
  rintro b rfl
  let b:=a.set droppedVar (a.env blockCount*a.env syndromeWidth)
  refine Hs.seq (t2:=1) (hs_copy C freeVar arity b (by decide)) ?_
  rintro d rfl
  let d:=b.set freeVar (b.env arity)
  have hdFree : d.env freeVar=r.child.call.n := by
    dsimp only [d]
    rw [DS.set_env_self]
    dsimp only [b]
    rw [DS.set_env_ne _ _ (by decide : arity≠droppedVar)]
    exact hn
  have hdDropped : d.env droppedVar=r.child.selected.1.r*r.child.selected.1.s := by
    dsimp only [d]
    rw [DS.set_env_ne _ _ (by decide : droppedVar≠freeVar)]
    dsimp only [b]
    rw [DS.set_env_self,hr,hs]
  refine (hs_sub C freeVar droppedVar d (by decide) (by rw [hdFree,hdDropped];exact hk)).mono le_rfl ?_
  rintro out rfl
  have hf : Fr a (d.set freeVar (d.env freeVar-d.env droppedVar)) [droppedVar,freeVar] :=
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨?_,(Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _)),
    Cst.of_fr hc hf (by decide)⟩
  change d.env freeVar-d.env droppedVar=_
  rw [hdFree,hdDropped,←rules.k_eq]

end NearQuarticWires.StageCarrierEnvelope
