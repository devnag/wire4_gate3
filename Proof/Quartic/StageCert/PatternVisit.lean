import Proof.Quartic.StageCert.PatternFlag
import Proof.Quartic.StageCert.IncidenceReset

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: a nonzero error digit
is converted to its original coordinate, whose incidence is recomputed
from both original gate lists before updating the side flag. -/
def visitPatternCoordinate : St VV := .seq setPatternCoordinate
  (.seq resetCoordinate (.seq readCoordinateCall keepNonheavy))

/-- `def:mask`, paper/paper.tex: the exact arithmetic
frame of one nonzero error-coordinate visit. -/
def patternVisitScratch : List (Fin VV) :=
  [coordinate,patternDigit,vPOS,censusTotal,vJ,patternFlag]++callScratch

/-- `def:mask` and `prop:time`, paper/paper.tex: one original pattern coordinate is checked by a physical raw
source scan, retaining the source word, witness and output exactly. -/
theorem visitPatternCoordinate_run (C : Ctx) (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P]
    (hflag : a.env patternFlag=bnat P) (hd : 1≤a.env patternDigit)
    (hcoord : a.env patternBlock*a.env patternBlockSize+(a.env patternDigit-1)<c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd) :
    Hs C visitPatternCoordinate a (1202*(C.cw.length+2)^3) (fun b =>
      b.env patternFlag=bnat (P ∧
        Cells.incidence (c.first.gates++c.second.gates)
          ⟨a.env patternBlock*a.env patternBlockSize+(a.env patternDigit-1),hcoord⟩
          <a.env heavyThreshold) ∧
      b.cp=pos3 c ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b patternVisitScratch) := by
  let i : Fin c.n := ⟨_,hcoord⟩
  unfold visitPatternCoordinate
  apply Hx.hs
  refine Hs.then (setPatternCoordinate_run C a hc hd (by omega))
    (fun r ⟨ri,rc,rw,ro,rf⟩ n1 hn1 => ?_)
  have rconst : Cst r := Cst.of_fr hc rf (by decide) (by rw [rf _ (by decide)]; exact hc.pos.trans rc.symm)
  refine Hs.then (resetCoordinate_run C r rconst)
    (fun s ⟨_se,sc,st,sw,so,sconst,sf⟩ n2 hn2 => ?_)
  have si : s.env coordinate=i.val := (sf _ (by decide)).trans ri
  refine Hs.then (readCoordinateCall_prefix_run C c i suffix s sconst sc st si hcw hW hL)
    (fun t ⟨tt,tc,tw,too,tconst,tf⟩ n3 hn3 => ?_)
  have tflag : t.env patternFlag=bnat P :=
    (tf _ (by decide)).trans ((sf _ (by decide)).trans ((rf _ (by decide)).trans hflag))
  refine Hs.last (keepNonheavy_run C t tconst P tflag)
    (fun u ⟨uf,uc,uw,uo,uconst,uff⟩ n4 hn4 => ?_)
  have tH : t.env heavyThreshold=a.env heavyThreshold :=
    (tf _ (by decide)).trans ((sf _ (by decide)).trans (rf _ (by decide)))
  refine ⟨⟨?_,uc.trans tc,uw.trans (tw.trans (sw.trans rw)),
    uo.trans (too.trans (so.trans ro)),uconst,?_⟩,?_⟩
  · simpa only [tt,tH] using uf
  · exact (rf.weaken (by simp only [patternVisitScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto)).trans
      ((sf.weaken (by simp only [patternVisitScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto)).trans
        ((tf.weaken (by intro y hy; exact List.mem_append_right _ hy)).trans
          (uff.weaken (by simp only [patternVisitScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto))))
  · have hp : 8≤(C.cw.length+2)^3 := by
      have := Nat.pow_le_pow_left (show 2≤C.cw.length+2 by omega) 3
      norm_num at this
      exact this
    omega

end NearQuarticWires.StageCert.Incidence
