import Proof.Quartic.StageMainMask.LengthRecordRead

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the three actual measured source lengths are fetched into retained
binary variables after the point computation has finished. -/
def loadLengthRecords : St VV MM :=
  .seq (readLengthRecord 0 39) (.seq (readLengthRecord 1 40) (readLengthRecord 2 41))

/-- `prop:time`, paper/paper.tex: fixed record
lookups preserve all point codes and original source data outside the
explicit memory-access and measured-length variables. -/
def lengthLoadScratch : List (Fin VV) := [t2, vJ, c0, 39, 40, 41]

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: all three actual source-length records are
read by paid rewinds and finite scans without a supplied numeric length. -/
theorem loadLengthRecords_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (prepared call header : ℕ) (hstore : a.ram entryLengthStore = [prepared, call, header])
    (hfit : 2 < 2 ^ C.Wd) :
    Hs C loadLengthRecords a (a.rc entryLengthStore + 100) (fun b =>
      b.env 39 = prepared ∧ b.env 40 = call ∧ b.env 41 = header ∧
      b.rc entryLengthStore = 3 ∧ lengthRecordRest b = lengthRecordRest a ∧
      Cst b ∧ Fr a b lengthLoadScratch) := by
  unfold loadLengthRecords
  apply Hx.hs
  refine Hs.then (readLengthRecord_run C [prepared, call, header] rfl 0 39 a hc hstore
    (by omega) (by decide)) (fun b ⟨hbv, hbrc, hbrest, hbc, hbfr⟩ n1 hn1 => ?_)
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hbrest
  refine Hs.then (readLengthRecord_run C [prepared, call, header] rfl 1 40 b hbc (hbram ▸ hstore)
    (by omega) (by decide)) (fun d ⟨hdv, hdrc, hdrest, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdram : d.ram = b.ram := congrArg (fun t => t.2.2.1) hdrest
  refine Hs.last (readLengthRecord_run C [prepared, call, header] rfl 2 41 d hdc
    (hdram ▸ hbram ▸ hstore) hfit (by decide)) ?_
  rintro e ⟨hev, herc, herest, hec, hefr⟩ n3 hn3
  have h39 : e.env 39 = prepared := by rw [hefr _ (by decide), hdfr _ (by decide), hbv]; rfl
  have h40 : e.env 40 = call := by rw [hefr _ (by decide), hdv]; rfl
  have h41 : e.env 41 = header := hev
  have hf1 : Fr a b lengthLoadScratch := hbfr.weaken (by
    intro x hx; simp only [lengthLoadScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have hf2 : Fr b d lengthLoadScratch := hdfr.weaken (by
    intro x hx; simp only [lengthLoadScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have hf3 : Fr d e lengthLoadScratch := hefr.weaken (by
    intro x hx; simp only [lengthLoadScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  refine ⟨⟨h39, h40, h41, herc, herest.trans (hdrest.trans hbrest), hec, hf1.trans (hf2.trans hf3)⟩, ?_⟩
  rw [hbrc] at hn2
  rw [hdrc] at hn3
  norm_num at hn1 hn2 hn3
  omega

end NearQuarticWires.StageMainMask
