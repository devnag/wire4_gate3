import Proof.Quartic.StageCert.CornerReplay

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `sec:cells`, paper/paper.tex: four evaluations all
read the same literal raw threshold gate, retaining its source offset. -/
def fourCorners : St VV := .seq (.op (.copy cornerGateStart vPOS))
  (.seq (replayCorner 0) (.seq (replayCorner 1) (.seq (replayCorner 2) (replayCorner 3))))

/-- `sec:cells`, paper/paper.tex: the complete four-corner
evaluation retains the four original packed source points. -/
def fourCornerScratch : List (Fin VV) :=
  [cornerGateStart,t0,vPOS,vJ,pointSaved,cornerBit 0,cornerBit 1,cornerBit 2,cornerBit 3]++scoreGateScratch

/-- `sec:cells` and `prop:time`, paper/paper.tex: the four literal raw-gate bits are computed exactly with a
uniform polynomial source cost and no precomputed gate-value input. -/
theorem fourCorners_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp=gateWord g++rest) (hbase : a.cp≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd) :
    Hs C fourCorners a (850*(C.cw.length+2)^2+30) (fun z =>
      (∀l,z.env (cornerBit l)=(g.eval (packedPoint n (a.env (cornerPoint l)))).toNat) ∧
      z.cp=a.cp+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z fourCornerScratch) := by
  unfold fourCorners
  apply Hx.hs
  refine Hs.then (hs_copy C cornerGateStart vPOS a (by decide))
    (fun r hr n0 hn0 => ?_)
  subst hr
  let r := a.set cornerGateStart (a.env vPOS)
  have rc : Cst r := Cst.of_fr hc (Fr.set (T := [cornerGateStart]) _ _ (by simp))
    (by decide) (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  have rb : r.env cornerGateStart=a.cp := by simp [r,hc.pos]
  have rf : FrS a r fourCornerScratch := (Fr.set (T := [cornerGateStart]) _ _ (by simp)).toS.weaken (by simp [fourCornerScratch])
  have rp : ∀l,r.env (cornerPoint l)=a.env (cornerPoint l) := by
    intro l
    exact rf _ (by fin_cases l <;> decide) (by fin_cases l <;> decide)
  refine Hs.then (replayCorner_run C g 0 r rc rest a.cp rb hin hbase hW
    (by rw [rp]; exact hpoint 0))
    (fun b ⟨b0,bc,bw,bo,bconst,bfr⟩ n1 hn1 => ?_)
  have bf : FrS a b fourCornerScratch := rf.trans (bfr.weaken (by decide))
  have bb : b.env cornerGateStart=a.cp := (bfr _ (by decide) (by decide)).trans rb
  have bp : ∀l,b.env (cornerPoint l)=a.env (cornerPoint l) := by
    intro l
    exact bf _ (by fin_cases l <;> decide) (by fin_cases l <;> decide)
  refine Hs.then (replayCorner_run C g 1 b bconst rest a.cp bb hin hbase hW
    (by rw [bp]; exact hpoint 1))
    (fun d ⟨d1,dc,dw,doo,dconst,dfr⟩ n2 hn2 => ?_)
  have df : FrS a d fourCornerScratch := bf.trans (dfr.weaken (by decide))
  have db : d.env cornerGateStart=a.cp := (dfr _ (by decide) (by decide)).trans bb
  have dp : ∀l,d.env (cornerPoint l)=a.env (cornerPoint l) := by
    intro l
    exact df _ (by fin_cases l <;> decide) (by fin_cases l <;> decide)
  refine Hs.then (replayCorner_run C g 2 d dconst rest a.cp db hin hbase hW
    (by rw [dp]; exact hpoint 2))
    (fun e ⟨e2,ec,ew,eo,econst,efr⟩ n3 hn3 => ?_)
  have ef : FrS a e fourCornerScratch := df.trans (efr.weaken (by decide))
  have eb : e.env cornerGateStart=a.cp := (efr _ (by decide) (by decide)).trans db
  have ep : ∀l,e.env (cornerPoint l)=a.env (cornerPoint l) := by
    intro l
    exact ef _ (by fin_cases l <;> decide) (by fin_cases l <;> decide)
  refine Hs.last (replayCorner_run C g 3 e econst rest a.cp eb hin hbase hW
    (by rw [ep]; exact hpoint 3))
    (fun z ⟨z3,zc,zw,zo,zconst,zfr⟩ n4 hn4 => ?_)
  refine ⟨⟨?_,zc,zw.trans (ew.trans (dw.trans (bw.trans (by rfl)))),
    zo.trans (eo.trans (doo.trans (bo.trans (by rfl)))),zconst,ef.trans (zfr.weaken (by decide))⟩,?_⟩
  · intro l
    fin_cases l
    · change z.env (cornerBit 0)=(g.eval (packedPoint n (a.env (cornerPoint 0)))).toNat
      rw [zfr _ (by decide) (by decide),efr _ (by decide) (by decide),
        dfr _ (by decide) (by decide),b0,rp]
    · change z.env (cornerBit 1)=(g.eval (packedPoint n (a.env (cornerPoint 1)))).toNat
      rw [zfr _ (by decide) (by decide),efr _ (by decide) (by decide),d1,bp]
    · change z.env (cornerBit 2)=(g.eval (packedPoint n (a.env (cornerPoint 2)))).toNat
      rw [zfr _ (by decide) (by decide),e2,dp]
    · change z.env (cornerBit 3)=(g.eval (packedPoint n (a.env (cornerPoint 3)))).toNat
      rw [z3,ep]
  · omega

end NearQuarticWires.StageCert
