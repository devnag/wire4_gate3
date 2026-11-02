import Proof.Quartic.StageResize.Cost
import Proof.Gates.TabMachine.Tuple

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms.SInt

/-- `lem:print`, paper/paper.tex: actual raw signed
field records, with proof-only width/fit data and a real end marker. -/
structure StreamResizeRequest where
  inputWidth : ℕ
  outputWidth : ℕ
  rows : List (List ℤ)
  input_pos : 0 < inputWidth
  output_pos : 0 < outputWidth
  width_le : inputWidth ≤ outputWidth
  fits : ∀ z ∈ rows.flatten, encS z < 2 ^ inputWidth

def numberRecords (width : ℕ) (values : List ℕ) : List Bool :=
  values.flatMap fun v => frame (binary width v)

def streamFlag (values : List ℕ) : Bool := !values.isEmpty

def streamPayload (width : ℕ) : List ℕ → List Bool
  | [] => []
  | v :: vs => StageLift.framePayload (binary width v) ++ numberRecords width vs ++ [false]

def StreamResizeRequest.values (r : StreamResizeRequest) : List ℕ :=
  r.rows.flatten.map encS

def StreamResizeRequest.fieldCount (r : StreamResizeRequest) : ℕ := r.rows.flatten.length

/-- `lem:print`, paper/paper.tex: no count, source
width or value is a runtime field; the end bit is actual paid input. -/
def StreamResizeRequest.word (r : StreamResizeRequest) : List Bool :=
  natWord r.outputWidth ++ fieldsRecs r.inputWidth r.rows ++ [false]

/-- `lem:print`, paper/paper.tex: raw output retains
all field delimiters and has no additional whole-stream frame. -/
def StreamResizeRequest.output (r : StreamResizeRequest) : List Bool :=
  fieldsRecs r.outputWidth r.rows

theorem fieldsRecs_eq_numberRecords (width : ℕ) (rows : List (List ℤ)) :
    fieldsRecs width rows = numberRecords width (rows.flatten.map encS) := by
  unfold fieldsRecs numberRecords
  rw [List.flatMap_map]
  rfl

theorem StreamResizeRequest.values_length (r : StreamResizeRequest) :
    r.values.length = r.fieldCount := by
  change (r.rows.flatten.map encS).length = r.rows.flatten.length
  exact List.length_map encS

theorem StreamResizeRequest.values_fit (r : StreamResizeRequest) :
    ∀ v ∈ r.values, v < 2 ^ r.inputWidth := by
  intro v hv
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
  exact r.fits z hz

theorem binary_flag_positive (width value : ℕ) (hwidth : 0 < width) :
    StageLift.frameFlag (binary width value) = true := by
  have hlen : 0 < (binary width value).length := by simpa using hwidth
  cases hb : binary width value with
  | nil => simp [hb] at hlen
  | cons bit bits => rfl

theorem stream_decompose (width : ℕ) (hwidth : 0 < width) (values : List ℕ) :
    numberRecords width values ++ [false] =
      streamFlag values :: streamPayload width values := by
  cases values with
  | nil => rfl
  | cons v vs =>
      simp only [numberRecords, List.flatMap_cons, List.append_assoc, streamFlag,
        List.isEmpty_cons, Bool.not_false, streamPayload]
      rw [StageLift.frame_decompose, binary_flag_positive width v hwidth]
      rfl

theorem numberRecords_length (width : ℕ) (values : List ℕ) :
    (numberRecords width values).length = (2 * width + 1) * values.length := by
  induction values with
  | nil => simp [numberRecords]
  | cons v vs ih =>
      simp only [numberRecords, List.flatMap_cons, List.length_append, frame_length,
        binary_length, List.length_cons] at *
      nlinarith

end NearQuarticWires.StageResize
