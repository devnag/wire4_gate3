import Proof.Quartic.StageHamming.DataPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def dataTarget : Fin VV := 95
def dataIndex : Fin VV := 96
def dataCount : Fin VV := 97
def dataAnswer : Fin VV := 98
def dataLimit : Fin VV := 99

def dataSelectScratch : List (Fin VV) := [dataCount, dataAnswer, vJ]

/-- `imp:partition`, paper/paper.tex: a nonparity
position increments the data-position count and is retained exactly
when that count is the requested index. -/
def dataSelect : St VV MM :=
  .ite (.eq parityFlag vZ)
    (.seq (.ite (.eq dataCount dataTarget) (.op (.copy dataAnswer dataIndex)) skipS)
      (.op (.inc dataCount))) skipS

/-- `imp:partition` and `prop:time`, paper/paper.tex: one scalar data-position selection uses only equality,
copying and increment, including the default-zero out-of-range case. -/
theorem dataSelect_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (j m c z : ℕ) (p : Bool)
    (hj : a.env dataIndex = j) (hm : a.env dataTarget = m)
    (hcount : a.env dataCount = c) (hanswer : a.env dataAnswer = z)
    (hflag : a.env parityFlag = p.toNat) (hbound : c + 1 < 2 ^ C.Wd) :
    Hs C dataSelect a 5 (fun b =>
      b.env dataCount = (if p then c else c + 1) ∧
      b.env dataAnswer = (if p then z else if m = c then j else z) ∧
      b.sh = a.sh ∧ Fr a b dataSelectScratch) := by
  cases p with
  | false =>
    have hchoose : Hs C (.ite (.eq dataCount dataTarget)
        (.op (.copy dataAnswer dataIndex)) skipS) a 2 (fun b =>
          b.env dataCount = c ∧ b.env dataAnswer = (if m = c then j else z) ∧
          b.sh = a.sh ∧ Fr a b [dataAnswer, vJ]) := by
      refine Hs.ite (c := .eq dataCount dataTarget)
        (show dataCount ≠ dataTarget by decide) ?_ ?_
      · intro he
        have heq : m = c := by
          have : c = m := by simpa only [Cnd.eval, hcount, hm, decide_eq_true_eq] using he
          exact this.symm
        refine Hs.mono (hs_copy C dataAnswer dataIndex a (by decide)) le_rfl ?_
        rintro b rfl
        exact ⟨by rw [DS.set_env_ne _ _ (by decide), hcount],
          by rw [DS.set_env_self, hj, if_pos heq], rfl, Fr.set _ _ (by simp)⟩
      · intro he
        have hne : m ≠ c := by
          have : c ≠ m := by simpa only [Cnd.eval, hcount, hm, decide_eq_false_iff_not] using he
          exact this.symm
        refine Hs.mono (skip_spec a) le_rfl ?_
        rintro b rfl
        exact ⟨by rw [DS.set_env_ne _ _ (by decide), hcount],
          by rw [DS.set_env_ne _ _ (by decide), hanswer, if_neg hne],
          rfl, Fr.set _ _ (by simp)⟩
    unfold dataSelect
    refine Hs.iteT (show parityFlag ≠ vZ by decide)
      (by simp [Cnd.eval, hflag, hc.z]) ?_
    refine Hs.seq (t1 := 2) (t2 := 1) hchoose (fun b hb => ?_)
    obtain ⟨hbcount, hbanswer, hbsh, hbfr⟩ := hb
    refine Hs.mono (hs_inc C dataCount b (by rw [hbcount]; exact hbound)) le_rfl ?_
    rintro d rfl
    exact ⟨by simp [hbcount], by rw [DS.set_env_ne _ _ (by decide)]; exact hbanswer,
      hbsh, (hbfr.weaken (by simp [dataSelectScratch])).trans (Fr.set _ _ (by simp [dataSelectScratch]))⟩
  | true =>
    unfold dataSelect
    refine Hs.mono (Hs.iteF (show parityFlag ≠ vZ by decide)
      (by simp [Cnd.eval, hflag, hc.z]) (skip_spec a))
      (by omega) ?_
    rintro b rfl
    exact ⟨by simp [DS.set_env_ne _ _ (by decide : dataCount ≠ vJ), hcount],
      by simp [DS.set_env_ne _ _ (by decide : dataAnswer ≠ vJ), hanswer],
      rfl, Fr.set _ _ (by simp [dataSelectScratch])⟩

end NearQuarticWires.StageHamming
