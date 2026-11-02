import Proof.Quartic.StageMainMask.MeasureHeader

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicGates.Close.Cells
open StageMain.Compact StageMain.CallSkip

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
three measured source lengths are retained in a disjoint actual record
store before coordinate arithmetic reuses the scanner variables. -/
def entryLengthStore : Fin MM := 7

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
actual preparation, call and prepared-header lengths are written as
three literal natural records, without encoding their numeric values
as unary tape material. -/
def recordEntryLengths : St VV MM :=
  .seq (.op (.wrM entryLengthStore compactLength))
    (.seq (.op (.wrM entryLengthStore lengthCounter)) (.op (.wrM entryLengthStore 41)))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the three measured source lengths are
physically saved with five source operations and all other stores intact. -/
theorem recordEntryLengths_run (C : Ctx) (a : DS VV MM)
    (hempty : a.ram entryLengthStore = [] ∧ a.rc entryLengthStore = 0) :
    Hs C recordEntryLengths a 5 (fun b =>
      b.ram entryLengthStore = [a.env compactLength, a.env lengthCounter, a.env 41] ∧
      b.rc entryLengthStore = 3 ∧ b.env = a.env ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      (∀ store, store ≠ entryLengthStore → b.ram store = a.ram store ∧ b.rc store = a.rc store)) := by
  unfold recordEntryLengths
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_wrM C entryLengthStore compactLength a (by rw [hempty.1, hempty.2]; simp)) ?_
  rintro b rfl
  let b := a.put entryLengthStore (a.env compactLength)
  have hb : b.ram entryLengthStore = [a.env compactLength] ∧ b.rc entryLengthStore = 1 := by
    simp [b, DS.put, hempty, putAt]
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_wrM C entryLengthStore lengthCounter b (by rw [hb.1, hb.2]; simp)) ?_
  rintro d rfl
  let d := b.put entryLengthStore (b.env lengthCounter)
  have hd : d.ram entryLengthStore = [a.env compactLength, a.env lengthCounter] ∧
      d.rc entryLengthStore = 2 := by
    simp [d, b, DS.put, hempty, putAt]
  refine (hs_wrM C entryLengthStore 41 d (by rw [hd.1, hd.2]; simp)).mono le_rfl ?_
  rintro e rfl
  refine ⟨?_, ?_, rfl, rfl, ?_⟩
  · simp [d, b, DS.put, hempty, putAt]
  · simp [d, b, DS.put, hempty]
  · intro store hs
    simp [d, b, DS.put, Function.update_of_ne hs]

end NearQuarticWires.StageMainMask
