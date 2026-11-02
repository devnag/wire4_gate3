import Proof.Quartic.StageCert.RecordRead

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `def:mask` and (W2), paper/paper.tex:
the actual retained witness selection begins immediately after its `k`
partition bits. -/
def selectionStart : Fin VV := ⟨107,by decide⟩

/-- `def:mask` and (W2), paper/paper.tex:
compute the original witness-bit address `k+g` for the current occurrence. -/
def prepareSelectionAddress : St VV MM :=
  .seq (.op (.copy sourceRecordLimit selectionStart))
    (.op (.add sourceRecordLimit atomOccurrence))

/-- `def:mask` and (W2), paper/paper.tex:
selection lookup uses a computed binary index while retaining the original
occurrence, partition width, actual stores and all external streams. -/
theorem prepareSelectionAddress_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (k g : ℕ) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hfit : k+g<2^C.Wd) :
    Hs C prepareSelectionAddress a 3 (fun z=>z.env sourceRecordLimit=k+g ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [sourceRecordLimit]) := by
  unfold prepareSelectionAddress
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_copy C sourceRecordLimit selectionStart a (by decide)) ?_
  rintro b rfl
  refine (hs_add C sourceRecordLimit atomOccurrence _ (by decide)
    (by vsimp [hk,hg]; exact hfit)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by vsimp [hk,hg],rfl,
    ⟨by vsimp [hc.z],by vsimp [hc.one],by vsimp [hc.two]⟩,
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageCert.Tokens
