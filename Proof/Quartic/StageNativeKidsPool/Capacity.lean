import Proof.Quartic.StageNativeKidsPool.ActualMeaning

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms
open StageTuple StageNativeKids

variable {R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
complete raw pool word retains actual count and target-width codecs,
all ordered original rows and one real stream delimiter. -/
def answer (F : Family R input) (records : R→List (List Bool)) (width : ℕ) : List Bool:=
  natWord F.count++natWord width++suffix (F.bytes records) 0 F.count++[false]

/-- `lem:print`, paper/paper.tex: a
finite proof capacity contains the actual source, original child count,
row clocks and final measured output; it is not a source input or a
loop over target-width or walk values. -/
def capacity (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) : ℕ:=
  10000*((frame F.source).length+(frame F.header).length+(natWord width).length+
    (natWord F.count).length+F.count+F.stepBudget budget+(answer F records width).length+1)

/-- `lem:print`, paper/paper.tex: the
actual original-child count fits the complete finite row-loop capacity. -/
theorem capacity_count (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) : F.count≤capacity F records budget width := by
  unfold capacity
  omega

/-- `lem:print`, paper/paper.tex: every
actual generated original-child input fits the same finite capacity. -/
theorem capacity_write (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width j : ℕ) (hj:j<F.count) :
    4*((frame F.source).length+(frame F.header).length)+8*j+100≤capacity F records budget width := by
  unfold capacity
  omega

/-- `lem:print`, paper/paper.tex: the
sum of actual row clocks pays every real row call and its input bytes
inside the common finite reusable-bank capacity. -/
theorem capacity_call (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) (j : Fin F.count) :
    2*(input (F.request j)).length+2+budget (F.request j)≤capacity F records budget width := by
  have hs:=F.step_le budget j
  unfold occurrenceCost StageTuple.callRecordsCost at hs
  unfold capacity
  omega

/-- `lem:print`, paper/paper.tex: source
copying fits by its actual framed byte count. -/
theorem capacity_source_copy (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) :
    4*F.source.length+4≤capacity F records budget width := by
  unfold capacity
  simp only [frame_length]
  omega

/-- `lem:print`, paper/paper.tex: the
actual small-count parser and copied binary codecs fit without a
numerical target-width bound. -/
theorem capacity_initialize (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) :
    4*(F.count+1)+2*(natWord F.count).length+(natWord width).length+20≤
      capacity F records budget width := by
  unfold capacity
  omega

/-- `lem:print`, paper/paper.tex: the
actual complete row suffix fits after its physically written two-codec
prefix, including the final real delimiter. -/
theorem capacity_suffix (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) :
    (natWord F.count).length+(natWord width).length+
      (suffix (F.bytes records) 0 F.count).length+1≤capacity F records budget width := by
  unfold capacity answer
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

/-- `lem:print`, paper/paper.tex: one
measured final outer frame fits the same actual finite capacity. -/
theorem capacity_frame (F : Family R input) (records : R→List (List Bool))
    (budget : R→ℕ) (width : ℕ) :
    2*(answer F records width).length+1≤capacity F records budget width := by
  unfold capacity
  omega

end NearQuarticWires.StageNativeKidsPool
