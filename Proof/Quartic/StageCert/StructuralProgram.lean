import Proof.Quartic.StageCert.PatternPairFields

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicGates.Close.Interfaces
open Incidence

/-- `def:mask`, paper/paper.tex: both canonical patterns
are scanned against the original raw source, and their exact side bits are
combined by the structural-mask disjunction. -/
def structuralProgram : St VV := .seq (preparePatternSide false)
  (.seq patternSideProgram (.seq (.op (.copy patternLeftResult patternFlag))
    (.seq (preparePatternSide true) (.seq patternSideProgram combinePatternSides))))

/-- `def:mask`, paper/paper.tex: the complete structural
test preserves every public field outside this fixed arithmetic frame. -/
def structuralScratch : List (Fin VV) :=
  patternOffset::patternInput::patternLeftResult::patternSideScratch

/-- `def:mask` and `prop:time`, paper/paper.tex: the structural mask is evaluated exactly from both original
raw gate lists and two canonical numeric pattern codes, with no supplied
incidence or heavy-coordinate table. -/
theorem structuralProgram_run (C : Ctx) (c : Call) (suffix : List Bool)
    (P : StarParams) (cut : ℕ) (u v : Fin ((P.b+1)^(P.r/2)))
    (a : DS VV) (hc : Cst a) (hb : 1≤P.b)
    (hcut : a.env heavyThreshold=cut) (hB : a.env patternBlockSize=P.b)
    (hR : a.env patternRadix=P.b+1) (hcount : a.env patternCount=P.r/2)
    (hu : a.env patternLeftInput=u.val) (hv : a.env patternRightInput=v.val)
    (hsource : P.b*P.r≤c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd)
    (hradix : 2*(P.b+1)≤2^C.Wd) (hrfit : P.r<2^C.Wd) :
    Hs C structuralProgram a (2*(P.r/2)*(1204*(C.cw.length+2)^3+2)+40) (fun z =>
      z.env patternFlag=(Mask.structuralMask (P.flipSet P.leftBlock) (P.flipSet P.rightBlock)
        (Mask.heavyCoordinates (fun i=>sourceDegree c i.val) cut)
        ((errorsEquiv P).symm u) ((errorsEquiv P).symm v)).toNat ∧
      z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z structuralScratch) := by
  let left := patternAvoids P (fun i=>sourceDegree c i.val) cut P.leftBlock u
  let right := patternAvoids P (fun i=>sourceDegree c i.val) cut P.rightBlock v
  have hlSource : P.b*(0+P.r/2)≤c.n := by
    exact (Nat.mul_le_mul_left P.b (show 0+P.r/2≤P.r by omega)).trans hsource
  have hrSource : P.b*(P.r/2+P.r/2)≤c.n := by rw [P.r_half_add]; exact hsource
  unfold structuralProgram
  apply Hx.hs
  refine Hs.then (preparePatternSide_run C a hc false)
    (fun r ⟨roff,ri,_rc,rw,ro,rconst,rf⟩ n1 hn1 => ?_)
  have rcut : r.env heavyThreshold=cut := (rf _ (by decide)).trans hcut
  have rB : r.env patternBlockSize=P.b := (rf _ (by decide)).trans hB
  have rR : r.env patternRadix=P.b+1 := (rf _ (by decide)).trans hR
  have rcount : r.env patternCount=P.r/2 := (rf _ (by decide)).trans hcount
  have rinput : r.env patternInput=u.val := by simpa only [Bool.false_eq_true,if_false,hu] using ri
  have rOffset : r.env patternOffset=0 := by simpa using roff
  refine Hs.then (patternSideProgram_run C c suffix P P.leftBlock 0 cut
    (by intro j; simp [StarParams.leftBlock]) u r rconst hb rcut rB rR rOffset rcount
    rinput hlSource hcw hW hL hn hradix (by omega))
    (fun s ⟨sl,sw,so,sconst,sf⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C patternLeftResult patternFlag s (by decide))
    (fun t ht n3 hn3 => ?_)
  subst ht
  let t := s.set patternLeftResult (s.env patternFlag)
  have tc : Cst t := Cst.of_fr sconst (Fr.set (T := [patternLeftResult]) _ _ (by simp))
    (by decide) (by rw [DS.set_env_ne _ _ (by decide)]; exact sconst.pos)
  have tf : Fr s t [patternLeftResult] := Fr.set _ _ (by simp)
  refine Hs.then (preparePatternSide_run C t tc true)
    (fun q ⟨qoff,qi,_qc,qw,qo,qconst,qf⟩ n4 hn4 => ?_)
  have qcut : q.env heavyThreshold=cut :=
    (qf _ (by decide)).trans ((tf _ (by decide)).trans ((sf _ (by decide)).trans rcut))
  have qB : q.env patternBlockSize=P.b :=
    (qf _ (by decide)).trans ((tf _ (by decide)).trans ((sf _ (by decide)).trans rB))
  have qR : q.env patternRadix=P.b+1 :=
    (qf _ (by decide)).trans ((tf _ (by decide)).trans ((sf _ (by decide)).trans rR))
  have qcount : q.env patternCount=P.r/2 :=
    (qf _ (by decide)).trans ((tf _ (by decide)).trans ((sf _ (by decide)).trans rcount))
  have qOffset : q.env patternOffset=P.r/2 := by
    simpa using qoff.trans
      ((tf _ (by decide)).trans ((sf _ (by decide)).trans rcount))
  have qinput : q.env patternInput=v.val := by
    simpa using qi.trans
      ((tf _ (by decide)).trans ((sf _ (by decide)).trans ((rf _ (by decide)).trans hv)))
  refine Hs.then (patternSideProgram_run C c suffix P P.rightBlock (P.r/2) cut
    (by intro j; rfl) v q qconst hb qcut qB qR qOffset qcount qinput hrSource
    hcw hW hL hn hradix (by rw [P.r_half_add]; exact hrfit))
    (fun d ⟨dr,dw,doo,dconst,df⟩ n5 hn5 => ?_)
  have dl : d.env patternLeftResult=left.toNat := by
    rw [df _ (by decide),qf _ (by decide)]
    exact sl
  refine Hs.last (combinePatternSides_run C d dconst left right dl dr)
    (fun z ⟨zf,_zc,zw,zo,zconst,zfr⟩ n6 hn6 => ?_)
  refine ⟨⟨?_,zw.trans (dw.trans (qw.trans (sw.trans rw))),
    zo.trans (doo.trans (qo.trans (so.trans ro))),zconst,?_⟩,?_⟩
  · rw [structuralMask_eq_patternAvoids]
    exact zf
  · exact (rf.weaken (by decide)).trans
      ((sf.weaken (by decide)).trans ((tf.weaken (by decide)).trans
        ((qf.weaken (by decide)).trans ((df.weaken (by decide)).trans (zfr.weaken (by decide))))))
  · have he : 2*(P.r/2)*(1204*(C.cw.length+2)^3+2)=
        2*((P.r/2)*(1204*(C.cw.length+2)^3+2)) := by ring
    rw [he]
    omega

end NearQuarticWires.StageCert
