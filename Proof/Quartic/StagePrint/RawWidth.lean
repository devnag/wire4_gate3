import Proof.Quartic.StagePrint.RawBankFormatter
import Proof.Gates.Dispatch.ParseCall

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch

/-- `lem:print`, paper/paper.tex: the original-child arithmetic width is computed from the actual parsed dimension and normalized coefficient height. -/
def setOriginalWidth : St VV := .seq (.op (.copy t3 vN)) (.seq (.op (.inc t3))
  (.seq clog2 (.seq (.op (.copy width vB0))
    (.seq (.op (.add width t5)) (incS width 5)))))

/-- `lem:print`, paper/paper.tex: computing the common original field width uses only declared arithmetic scratch registers. -/
def widthScratch : List (Fin VV) := [t3,t5,t6,width,vJ]

/-- `lem:print` and `prop:time`, paper/paper.tex: no caller-supplied field width is needed after the original call header has been physically parsed. -/
theorem setOriginalWidth_run (C : Ctx) (a : DS VV) (hc : Cst a) (n B : ℕ)
    (hn : a.env vN=n) (hB : a.env vB0=B)
    (hfit : 2*(n+1)+2<2^C.Wd) (hwidth : B+Nat.clog 2 (n+1)+5<2^C.Wd) :
    Hs C setOriginalWidth a (5*Nat.clog 2 (n+1)+30) (fun b=>
      b.env width=originalFieldWidth n B+1 ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      b.out=a.out ∧ Cst b ∧ Fr a b widthScratch) := by
  unfold setOriginalWidth
  refine Hx.hs (Hs.then (hs_copy C t3 vN a (by decide)) (fun b hb n1 hn1=>?_))
  subst hb
  refine Hs.then (hs_inc C t3 _ (by simp [hn];omega)) (fun e he n2 hn2=>?_)
  subst he
  let e:DS VV:=(a.set t3 (a.env vN)).set t3 ((a.set t3 (a.env vN)).env t3+1)
  have ef : Fr a e [t3] := (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))
  have ec : Cst e:=Cst.of_fr hc ef (by decide)
    (by rw [ef vPOS (by decide)];exact hc.pos)
  have en : e.env t3=n+1 := by simp [e,hn]
  refine Hs.then (clog2_spec (C:=C) e ec (by rw [en];exact hfit))
    (fun f ⟨fv,_,fp,fw,fo,fc,ff⟩ n3 hn3=>?_)
  rw [en] at fv hn3
  have fB : f.env vB0=B := by rw [ff vB0 (by decide),ef vB0 (by decide)];exact hB
  refine Hs.then (hs_copy C width vB0 f (by decide)) (fun g hg n4 hn4=>?_)
  subst hg
  let g:=f.set width (f.env vB0)
  have gf : Fr f g [width] := Fr.set _ _ (by simp)
  have gc : Cst g:=Cst.of_fr fc gf (by decide)
    (by rw [gf vPOS (by decide)];exact fc.pos)
  have gv : g.env width=B := by simp [g,fB]
  have gt : g.env t5=Nat.clog 2 (n+1) := by rw [gf t5 (by decide)];exact fv
  refine Hs.then (hs_add C width t5 g (by decide) (by rw [gv,gt];omega))
    (fun j hj n5 hn5=>?_)
  subst hj
  let j:=g.set width (g.env width+g.env t5)
  have jf : Fr g j [width] := Fr.set _ _ (by simp)
  have jc : Cst j:=Cst.of_fr gc jf (by decide)
    (by rw [jf vPOS (by decide)];exact gc.pos)
  have jv : j.env width=B+Nat.clog 2 (n+1) := by simp [j,gv,gt]
  refine Hs.last (incS_spec (C:=C) width (by decide) 5 j (by rw [jv];exact hwidth))
    (fun k ⟨kv,kp,kw,ko,kf⟩ n6 hn6=>?_)
  have kc : Cst k:=Cst.of_fr jc kf (by decide)
    (by rw [kf vPOS (by decide),jc.pos,kp])
  refine ⟨⟨?_,?_,?_,?_,kc,?_⟩,?_⟩
  · rw [kv,jv];unfold originalFieldWidth;omega
  · simpa only [j,g,e,DS.set_cp] using kp.trans fp
  · simpa only [j,g,e,DS.set_wq] using kw.trans fw
  · simpa only [j,g,e,DS.set_out] using ko.trans fo
  · exact (ef.weaken (by decide)).trans ((ff.weaken (by decide)).trans
      ((gf.weaken (by decide)).trans ((jf.weaken (by decide)).trans (kf.weaken (by decide)))))
  · omega

end NearQuarticWires.StagePrint.RawBits
