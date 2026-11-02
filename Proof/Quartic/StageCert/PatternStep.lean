import Proof.Quartic.StageCert.PatternCheck

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: one pattern slot removes
the least-significant digit, checks its actual original coordinate, and
advances the original block index. -/
def patternStep : St VV := .seq nextPatternDigit
  (.seq checkPatternDigit (.op (.inc patternBlock)))

/-- `def:mask`, paper/paper.tex: registers modified by
one complete numeric pattern iteration. -/
def patternStepScratch : List (Fin VV) :=
  patternCode::patternQuotient::patternBlock::patternVisitScratch

/-- `def:mask` and `prop:time`, paper/paper.tex: every slot has an exact quotient, original-coordinate flag and
uniform polynomial source-scan cost, including zero error digits. -/
theorem patternStep_run (C : Ctx) (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P]
    (hflag : a.env patternFlag=bnat P)
    (hq : 0<a.env patternRadix) (hfit : 2*a.env patternRadix≤2^C.Wd)
    (hcoord : a.env patternCode%a.env patternRadix≠0 →
      a.env patternBlock*a.env patternBlockSize+(a.env patternCode%a.env patternRadix-1)<c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hblock : a.env patternBlock+1<2^C.Wd) :
    Hs C patternStep a (1204*(C.cw.length+2)^3) (fun b =>
      b.env patternCode=a.env patternCode/a.env patternRadix ∧
      b.env patternBlock=a.env patternBlock+1 ∧
      b.env patternFlag=bnat (P ∧ digitNonheavy c (a.env heavyThreshold)
        (a.env patternBlockSize) (a.env patternBlock) (a.env patternCode%a.env patternRadix)) ∧
      b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b patternStepScratch) := by
  unfold patternStep
  apply Hx.hs
  refine Hs.then (nextPatternDigit_run C a hq hfit)
    (fun r ⟨rCode,rDigit,rc,rw,ro,rf⟩ n1 hn1 => ?_)
  have rconst : Cst r := Cst.of_fr hc rf (by decide)
    (by rw [rf _ (by decide)]; exact hc.pos.trans rc.symm)
  have rflag : r.env patternFlag=bnat P := (rf _ (by decide)).trans hflag
  have rb : r.env patternBlock=a.env patternBlock := rf _ (by decide)
  have rB : r.env patternBlockSize=a.env patternBlockSize := rf _ (by decide)
  have rH : r.env heavyThreshold=a.env heavyThreshold := rf _ (by decide)
  have rcoord : r.env patternDigit≠0 →
      r.env patternBlock*r.env patternBlockSize+(r.env patternDigit-1)<c.n := by
    simpa only [rb,rB,rDigit] using hcoord
  refine Hs.then (checkPatternDigit_run C c suffix r rconst P rflag rcoord hcw hW hL hn)
    (fun s ⟨sf,sw,so,sconst,sfr⟩ n2 hn2 => ?_)
  have sb : s.env patternBlock=a.env patternBlock := (sfr _ (by decide)).trans rb
  have sCode : s.env patternCode=a.env patternCode/a.env patternRadix :=
    (sfr _ (by decide)).trans rCode
  refine Hs.last (hs_inc C patternBlock s (by rw [sb]; exact hblock))
    (fun t ht n3 hn3 => ?_)
  subst ht
  refine ⟨⟨by rw [DS.set_env_ne _ _ (by decide)]; exact sCode,
    by simp only [DS.set_env_self,sb],?_,sw.trans rw,so.trans ro,?_,?_⟩,?_⟩
  · rw [DS.set_env_ne _ _ (by decide),sf,rH,rB,rb,rDigit]
  · exact Cst.of_fr sconst (Fr.set (T := [patternBlock]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact sconst.pos)
  · exact (rf.weaken (by simp only [patternStepScratch,patternVisitScratch,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false]; tauto)).trans
      ((sfr.weaken (by intro y hy; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hy)))).trans (Fr.set _ _ (by simp [patternStepScratch])))
  · have hp : 8≤(C.cw.length+2)^3 := by
      have := Nat.pow_le_pow_left (show 2≤C.cw.length+2 by omega) 3
      norm_num at this
      exact this
    omega

end NearQuarticWires.StageCert.Incidence
