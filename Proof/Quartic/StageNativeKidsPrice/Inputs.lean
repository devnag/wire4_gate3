import Proof.Quartic.StageNativeKidsPrice.Polynomial
import Proof.Quartic.StageNativeKids.RoleValid

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Dispatch
open StageNativeKids StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: the two
actual original bank cases retain the complete request and bank inequality. -/
structure SourceCase where
  request : NativeKidsRequest
  second : Bool
  bank : if second then request.header.call.first.gates.length ≤
    (request.toRowContext.originalIndex request.atom).val else
    (request.toRowContext.originalIndex request.atom).val < request.header.call.first.gates.length

/-- `lem:print`, paper/paper.tex: the case
selects the existing concrete original-source counter input. -/
def SourceCase.source : (a : SourceCase) → RawBits.IndexedCallGateRequest a.second
  | ⟨r, false, h⟩ => firstCountSource r h
  | ⟨r, true, h⟩ => secondCountSource r h

/-- `prop:time`, paper/paper.tex: the resource
is the original request length, original arity and unchanged sharp child cap. -/
def SourceCase.scale (a : SourceCase) : ℕ := a.request.originalSourceScale

/-- `prop:time`, paper/paper.tex: the
structural resource is positive for every actual request. -/
theorem scale_pos (a : SourceCase) : 1 ≤ a.scale := by
  unfold SourceCase.scale NativeKidsRequest.originalSourceScale
  omega

/-- `lem:print`, paper/paper.tex: both bank
cases retain exactly the original call. -/
theorem source_call (a : SourceCase) : a.source.call = a.request.header.call := by
  rcases a with ⟨r, b, h⟩
  cases b <;> rfl

/-- `lem:print`, paper/paper.tex: the
selected original gate uses its unchanged exact-child compiler request. -/
theorem source_child (a : SourceCase) : a.source.child =
    originalChildRequest (Call.B0 a.request.header.call.n)
      (callAtoms a.request.header.call (a.request.toRowContext.originalIndex a.request.atom))
      (a.request.gate_bits (a.request.toRowContext.originalIndex a.request.atom)) := by
  rcases a with ⟨r, b, h⟩
  cases b
  · exact firstCountSource_child r h
  · exact secondCountSource_child r h

/-- `lem:print`, paper/paper.tex: no suffix
is supplied to either actual source selector. -/
theorem source_suffix (a : SourceCase) : a.source.suffix = [] := by
  rcases a with ⟨r, b, h⟩
  cases b <;> rfl

/-- `lem:print`, paper/paper.tex: the
original input width and original arity have uniform structural prices. -/
theorem source_sizes (a : SourceCase) :
    a.source.child.weights.length = a.request.header.call.n ∧
      a.source.child.W ≤ 16 * (a.request.header.call.n + 1)^2 := by
  rw [source_child]
  constructor
  · simp only [originalChildRequest, List.length_ofFn]
  · have hlog : Nat.clog 2 (a.request.header.call.n+1) ≤ a.request.header.call.n+1 := by
      apply Nat.clog_le_of_le_pow
      exact Nat.lt_two_pow_self.le
    change Call.B0 a.request.header.call.n + Nat.clog 2 (a.request.header.call.n+1)+4 ≤ _
    unfold Call.B0
    have hm := Nat.mul_le_mul_left (4*a.request.header.call.n+1) hlog
    nlinarith only [hm]

/-- `lem:print`, paper/paper.tex: an actual
relative bank index is bounded by the original occurrence census. -/
theorem source_index (a : SourceCase) :
    a.source.index.val ≤ 2 * a.request.header.call.n^4 := by
  have hG := original_count_bound a.request.toRowContext
  have hi := (a.request.toRowContext.originalIndex a.request.atom).isLt
  rcases a with ⟨r, b, h⟩
  dsimp only at hG hi
  cases b
  · change (r.toRowContext.originalIndex r.atom).val ≤ 2*r.header.call.n^4
    omega
  · change (r.toRowContext.originalIndex r.atom).val-r.header.call.first.gates.length ≤ 2*r.header.call.n^4
    omega

/-- `lem:print`, paper/paper.tex: each
selected bank is bounded by the same original occurrence census. -/
theorem source_bank (a : SourceCase) :
    (RawBits.originalCircuit a.second a.source.call).gates.length ≤
      2 * a.request.header.call.n^4 := by
  have hG := original_count_bound a.request.toRowContext
  simp only [Builder.allGates, List.length_append] at hG
  rw [source_call]
  rcases a with ⟨r, b, h⟩
  dsimp only at hG
  cases b <;> change _ ≤ 2 * r.header.call.n^4 <;>
    simp only [RawBits.originalCircuit, Bool.false_eq_true, if_false, if_true] <;> omega

/-- `lem:print`, paper/paper.tex: the actual
source word contains the full original call as a literal framed field. -/
theorem call_length (r : NativeKidsRequest) : (callWord r.header.call).length ≤ r.word.length := by
  simp [NativeKidsRequest.word, NativeKidsRequest.sourceFields,
    NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadRec,
    RepairOrdinary.frame_length]
  omega

/-- `prop:time`, paper/paper.tex: original
arity has a direct linear structural price. -/
theorem arity_price : Price SourceCase.scale (fun a => a.request.header.call.n) :=
  Price.of_le (by intro a; unfold SourceCase.scale NativeKidsRequest.originalSourceScale; omega)

/-- `prop:time`, paper/paper.tex: the
literal original call length has a direct structural price. -/
theorem call_price : Price SourceCase.scale (fun a => (callWord a.request.header.call).length) :=
  Price.of_le (by
    intro a
    have h := call_length a.request
    unfold SourceCase.scale NativeKidsRequest.originalSourceScale
    omega)

end NearQuarticWires.StageNativeKidsPrice
