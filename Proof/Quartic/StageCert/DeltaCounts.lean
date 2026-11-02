import Proof.Quartic.StageCert.CornerGate

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch

/-- `sec:cells`, paper/paper.tex: the positive terms in
the original mixed difference are the center and both-error gate bits. -/
def deltaPositive : Fin VV := ⟨132,by decide⟩
/-- `sec:cells`, paper/paper.tex: the two one-sided gate
bits are the negative terms in the original mixed difference. -/
def deltaNegative : Fin VV := ⟨133,by decide⟩
/-- `def:mask`, paper/paper.tex: the occurrence's exact
absolute mixed difference is retained as a natural population contribution. -/
def deltaMagnitude : Fin VV := ⟨134,by decide⟩

/-- `sec:cells`, paper/paper.tex: the two signed counts
are formed directly from the four computed raw-gate bits. -/
def deltaCounts : St VV := .seq (.op (.copy deltaPositive (cornerBit 0)))
  (.seq (.op (.add deltaPositive (cornerBit 3)))
    (.seq (.op (.copy deltaNegative (cornerBit 1))) (.op (.add deltaNegative (cornerBit 2)))))

/-- `sec:cells`, paper/paper.tex: forming the signed
counts has constant physical arithmetic cost and retains all four bits. -/
theorem deltaCounts_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (hb : ∀l,a.env (cornerBit l)≤1) (hfit : 2<2^C.Wd) :
    Hs C deltaCounts a 7 (fun z =>
      z.env deltaPositive=a.env (cornerBit 0)+a.env (cornerBit 3) ∧
      z.env deltaNegative=a.env (cornerBit 1)+a.env (cornerBit 2) ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z [deltaPositive,deltaNegative]) := by
  unfold deltaCounts
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_copy C deltaPositive (cornerBit 0) a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_add C deltaPositive (cornerBit 3) _ (by decide)
    (by vsimp [deltaPositive,cornerBit]; have h0 := hb 0; have h3 := hb 3
        change a.env ⟨128,by decide⟩≤1 at h0
        change a.env ⟨131,by decide⟩≤1 at h3
        omega)) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C deltaNegative (cornerBit 1) _ (by decide)) ?_
  rintro e rfl
  refine (hs_add C deltaNegative (cornerBit 2) _ (by decide)
    (by vsimp [deltaPositive,deltaNegative,cornerBit]; have h1 := hb 1; have h2 := hb 2
        change a.env ⟨129,by decide⟩≤1 at h1
        change a.env ⟨130,by decide⟩≤1 at h2
        omega)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,rfl,rfl,?_,?_⟩
  · vsimp [deltaPositive,deltaNegative,cornerBit]
  · vsimp [deltaPositive,deltaNegative,cornerBit]
  · exact ⟨by vsimp [deltaPositive,deltaNegative,cornerBit,hc.z],
      by vsimp [deltaPositive,deltaNegative,cornerBit,hc.one],
      by vsimp [deltaPositive,deltaNegative,cornerBit,hc.two],
      by vsimp [deltaPositive,deltaNegative,cornerBit,hc.pos]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))

end NearQuarticWires.StageCert
