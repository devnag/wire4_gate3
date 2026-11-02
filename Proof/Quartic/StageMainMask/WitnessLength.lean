import Proof.Quartic.StageMainMask.LengthRecordsLoad

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual witness length is decoded from the difference between
measured preparation and header lengths, including its frame delimiter. -/
def decodeWitnessLength : St VV MM := .seq (.op (.copy 42 39))
  (.seq (.op (.sub 42 41)) (.seq (.op (.sub 42 v1)) (.op (.half 42))))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: native subtraction and halving recover the
exact finite witness payload length from the physically measured frame. -/
theorem decodeWitnessLength_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (prepared header witness : ℕ) (hprepared : a.env 39 = prepared)
    (hheader : a.env 41 = header) (hframe : prepared = header + 2 * witness + 1) :
    Hs C decodeWitnessLength a 7 (fun b => b.env 42 = witness ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [42]) := by
  unfold decodeWitnessLength
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_copy C 42 39 a (by decide)) ?_
  rintro b rfl
  let b := a.set 42 (a.env 39)
  have hb : b.env 42 = prepared := by simp [b, hprepared]
  have hbh : b.env 41 = header := (DS.set_env_ne _ _ (by decide)).trans hheader
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_sub C 42 41 b (by decide) (by rw [hb, hbh]; omega)) ?_
  rintro d rfl
  let d := b.set 42 (b.env 42 - b.env 41)
  have hd : d.env 42 = 2 * witness + 1 := by simp only [d, DS.set_env_self, hb, hbh]; omega
  have hdc : Cst d := hc.of_fr ((Fr.set (T := [42]) a _ (by simp)).trans (Fr.set b _ (by simp))) (by decide)
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C 42 v1 d (by decide) (by rw [hd, hdc.one]; omega)) ?_
  rintro e rfl
  let e := d.set 42 (d.env 42 - d.env v1)
  have he : e.env 42 = 2 * witness := by simp only [e, DS.set_env_self, hd, hdc.one]; omega
  refine (hs_half C 42 e).mono le_rfl ?_
  rintro f rfl
  have hf : Fr a (e.set 42 (e.env 42 / 2)) [42] :=
    (Fr.set a _ (by simp)).trans ((Fr.set b _ (by simp)).trans
      ((Fr.set d _ (by simp)).trans (Fr.set e _ (by simp))))
  exact ⟨by simp [he], rfl, hc.of_fr hf (by decide), hf⟩

end NearQuarticWires.StageMainMask
