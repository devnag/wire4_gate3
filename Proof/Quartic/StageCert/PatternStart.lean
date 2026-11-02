import Proof.Quartic.StageCert.PatternLoop

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch

/-- `def:mask`, paper/paper.tex: the original first block
of the side whose pattern is currently checked. -/
def patternOffset : Fin VV := ⟨108,by decide⟩
/-- `def:mask`, paper/paper.tex: the exact number of
original block slots on each side. -/
def patternCount : Fin VV := ⟨109,by decide⟩
/-- `def:mask`, paper/paper.tex: the canonical numeric
pattern code is retained separately from its successively decoded quotient. -/
def patternInput : Fin VV := ⟨110,by decide⟩

/-- `def:mask`, paper/paper.tex: exact initialization of
the numeric side-loop counters and empty conjunction flag. -/
def startPattern : St VV := .seq (.op (.copy patternBlock patternOffset))
  (.seq (.op (.copy patternEnd patternOffset))
    (.seq (.op (.add patternEnd patternCount))
      (.seq (.op (.copy patternCode patternInput)) (.op (.copy patternFlag v1)))))

/-- `def:mask`, paper/paper.tex: the side-loop setup
modifies only its counters, working quotient and accumulated flag. -/
def patternStartScratch : List (Fin VV) := [patternBlock,patternEnd,patternCode,patternFlag]

/-- `def:mask` and `prop:time`, paper/paper.tex: side initialization is a fixed physical arithmetic program,
retaining every original public field, witness bit and output byte. -/
theorem startPattern_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (hfit : a.env patternOffset+a.env patternCount<2^C.Wd) :
    Hs C startPattern a 9 (fun z =>
      z.env patternBlock=a.env patternOffset ∧
      z.env patternEnd=a.env patternOffset+a.env patternCount ∧
      z.env patternCode=a.env patternInput ∧ z.env patternFlag=1 ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z patternStartScratch) := by
  unfold startPattern
  refine Hs.seq (t1 := 1) (t2 := 7) (hs_copy C patternBlock patternOffset a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_copy C patternEnd patternOffset _ (by decide)) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_add C patternEnd patternCount _ (by decide)
    (by vsimp [patternBlock,patternOffset,patternEnd,patternCount]; exact hfit)) ?_
  rintro e rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C patternCode patternInput _ (by decide)) ?_
  rintro f rfl
  refine (hs_copy C patternFlag v1 _ (by decide)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,?_,?_,rfl,rfl,rfl,?_,?_⟩
  · vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag]
  · vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag]
  · vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag]
  · vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag,hc.one]
  · exact ⟨by vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag,hc.z],
      by vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag,hc.one],
      by vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag,hc.two],
      by vsimp [patternBlock,patternOffset,patternEnd,patternCount,patternCode,patternInput,patternFlag,hc.pos]⟩
  · exact (Fr.set _ _ (by simp [patternStartScratch])).trans
      ((Fr.set _ _ (by simp [patternStartScratch])).trans
        ((Fr.set _ _ (by simp [patternStartScratch])).trans
          ((Fr.set _ _ (by simp [patternStartScratch])).trans
            (Fr.set _ _ (by simp [patternStartScratch])))))

end NearQuarticWires.StageCert.Incidence
