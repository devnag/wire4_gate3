import Proof.Quartic.StageMainMask.RecordLengths
import Proof.Gates.Cells.Load2

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
a fixed measured-source length is read by actual rewind and finite
record scans from the disjoint length store. -/
def readLengthRecord (i : Fin 3) (dst : Fin VV) : St VV MM :=
  .seq (setK t2 i.val) (fetch entryLengthStore t2 dst)

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
only the source-length cursor is omitted from the retained state. -/
def lengthRecordRest (a : DS VV MM) :=
  (a.ip, a.out, a.ram, Function.update a.rc entryLengthStore 0, a.kin, a.kout, a.kc)

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: a measured length is physically fetched
with all rewind work charged and all other retained records intact. -/
theorem readLengthRecord_run (C : Ctx) (values : List ℕ) (hlen : values.length = 3)
    (i : Fin 3) (dst : Fin VV) (a : DS VV MM) (hc : Cst a)
    (hstore : a.ram entryLengthStore = values) (hfit : i.val < 2 ^ C.Wd)
    (hdst : dst ∉ [vZ, v1, v2]) :
    Hs C (readLengthRecord i dst) a (a.rc entryLengthStore + 7 * i.val + 13) (fun b =>
      b.env dst = values.getD i.val 0 ∧ b.rc entryLengthStore = i.val + 1 ∧
      lengthRecordRest b = lengthRecordRest a ∧ Cst b ∧ Fr a b [t2, vJ, c0, dst]) := by
  unfold readLengthRecord
  refine (Hs.seq (t2 := a.rc entryLengthStore + 5 * i.val + 9)
    (setK_spec t2 (by decide) i.val a hfit) ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbi, hbsh, hbfr⟩
  have hsame := Same.of_sh hbsh
  have hf := fetch_spec (C := C) entryLengthStore t2 dst (by decide) (by decide) b
    (by rw [hbi, hsame.ram, hstore, hlen]; exact i.isLt) (by rw [hbi]; exact hfit)
  rw [hsame.rc, hbi] at hf
  refine hf.mono le_rfl ?_
  rintro d ⟨hdv, hdip, hdout, hdram, hdrc, hdkin, hdkout, hdkc, hdfr⟩
  have hframes : Fr a d [t2, vJ, c0, dst] :=
    (hbfr.weaken (by simp)).trans (hdfr.weaken (by simp))
  refine ⟨?_, ?_, ?_, hc.of_fr hframes ?_, hframes⟩
  · rw [hdv, hsame.ram, hstore]
  · rw [hdrc, Function.update_self]
  · simp only [lengthRecordRest, hdip, hdout, hdram, hdrc, hdkin, hdkout, hdkc,
      hsame.ip, hsame.out, hsame.ram, hsame.kin, hsame.kout, hsame.kc, Function.update_idem]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdst ⊢
    exact ⟨⟨by decide, by decide, by decide, Ne.symm hdst.1⟩,
      ⟨by decide, by decide, by decide, Ne.symm hdst.2.1⟩,
      by decide, by decide, by decide, Ne.symm hdst.2.2⟩

end NearQuarticWires.StageMainMask
