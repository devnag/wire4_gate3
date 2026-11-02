import Proof.Quartic.StageHamming.DataSelect

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def dataParityScratch : List (Fin VV) := parityInput :: parityScratch
def dataStepScratch : List (Fin VV) := dataCount :: dataAnswer :: dataParityScratch

/-- `imp:partition`, paper/paper.tex: one original
block coordinate is tested for parity and then entered into the
increasing data-position lookup by its scalar rank. -/
def dataPositionStep : St VV MM :=
  .seq (.op (.copy parityInput dataIndex)) (.seq parityPosition dataSelect)

/-- `imp:partition` and `prop:time`, paper/paper.tex: each actual data-position scan step realizes the literal
filtered-list update, with all non-scratch registers preserved. -/
theorem dataPositionStep_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (j s m : ℕ) (hj : a.env dataIndex = j) (hswidth : a.env parityWidth = s)
    (hm : a.env dataTarget = m)
    (hcount : a.env dataCount = (dataPrefix s j).length)
    (hanswer : a.env dataAnswer = (dataPrefix s j).getD m 0)
    (hjW : j + 1 < 2 ^ C.Wd) (hs : s < 2 ^ C.Wd)
    (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C dataPositionStep a (8 * s + 20) (fun b =>
      b.env dataCount = (dataPrefix s (j + 1)).length ∧
      b.env dataAnswer = (dataPrefix s (j + 1)).getD m 0 ∧
      b.sh = a.sh ∧ Fr a b dataStepScratch) := by
  unfold dataPositionStep
  refine Hx.hs (Hs.then (hs_copy C parityInput dataIndex a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let b := a.set parityInput (a.env dataIndex)
  have hf0 : Fr a b dataParityScratch := Fr.set _ _ (by simp [dataParityScratch])
  have hcb : Cst b := hc.of_fr hf0 (by decide)
  refine Hs.then (parityPosition_spec b hcb j s
    (by rw [DS.set_env_self, hj])
    ((hf0 _ (by decide)).trans hswidth) hjW hs hW)
    (fun c hcp n2 hn2 => ?_)
  obtain ⟨hflag, hsh, hfr⟩ := hcp
  have hf : Fr a c dataParityScratch := hf0.trans (hfr.weaken (by decide))
  have hcc : Cst c := hc.of_fr hf (by decide)
  have hnext : (dataPrefix s j).length + 1 < 2 ^ C.Wd :=
    (Nat.add_le_add_right (dataPrefix_length_le s j) 1).trans_lt hjW
  refine Hs.last (dataSelect_spec c hcc j m (dataPrefix s j).length
    ((dataPrefix s j).getD m 0) (parityPrefix j s)
    ((hf _ (by decide)).trans hj) ((hf _ (by decide)).trans hm)
    ((hf _ (by decide)).trans hcount) ((hf _ (by decide)).trans hanswer)
    hflag hnext) ?_
  rintro d ⟨hdcount, hdanswer, hdsh, hdfr⟩ n3 hn3
  refine ⟨⟨?_, ?_, hdsh.trans hsh,
    (hf.weaken (by decide)).trans (hdfr.weaken (by decide))⟩, by omega⟩
  · cases hp : parityPrefix j s <;>
      simpa [dataPrefix_succ, hp] using hdcount
  · rw [dataPrefix_getD_succ]
    exact hdanswer

end NearQuarticWires.StageHamming
