import Proof.Quartic.StageMain.ActualSample
import Proof.Quartic.StageMain.CompactLayout

/-!
# One numeric entry of the sampled main pass

Step 4 of `sec:algorithm`, paper/paper.tex,
evaluates the predicate and the exact Boolean mask at a sample in a
column. The request contains the original finite preparation word,
the column number and the field value of the sample.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces

structure EntryRequest (B1 B2 : ℕ) where
  call : Call
  selected : Program.Selected call
  dispatched : Program.dispatch B1 B2 call = some selected
  witness : List Bool
  column : Fin (2 ^ (call.n - selected.1.k))
  fieldValue : Fin (2 ^ selected.1.ellf)

noncomputable def entryCall {B1 B2 : ℕ} (r : EntryRequest B1 B2) : Algorithm.CellCall :=
  Program.runCall r.call r.selected r.witness

noncomputable def entryPosition {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    Sampler.Cell (entryCall r).seed.N :=
  (entryCall r).seed.cellEquiv (fun b => GF.bitF (r.fieldValue.val.testBit b))

noncomputable def entryWord {B1 B2 : ℕ} (r : EntryRequest B1 B2) : List Bool :=
  Program.prepWord B1 B2 r.call r.witness ++
    natWord r.column.val ++ natWord r.fieldValue.val

noncomputable def entryPredicate {B1 B2 : ℕ} (r : EntryRequest B1 B2) : Bool :=
  (entryCall r).pred r.column (entryPosition r)

noncomputable def entryMask {B1 B2 : ℕ} (r : EntryRequest B1 B2) : Bool :=
  decide ((entryCall r).pointMask r.column (entryPosition r) = 1)

noncomputable def entryOutput {B1 B2 : ℕ} (r : EntryRequest B1 B2) : List Bool :=
  frame [entryPredicate r, entryMask r]

noncomputable def sampledEntryRequest {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q) : EntryRequest B1 B2 where
  call := c
  selected := p
  dispatched := hd
  witness := w
  column := z
  fieldValue := ⟨JoinElimination.gen (Program.runCall c p w).seed.modulus p.1.ellf 8
    (Algorithm.CellCall.prefixValue (Program.runCall c p w).chosenSeed) j.val,
    actualSampleValue_lt (Program.runCall c p w).seed _ j⟩

theorem sampledEntry_position {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q) :
    entryPosition (sampledEntryRequest hd w z j) = (Program.runCall c p w).samples j := by
  exact (actualSamplePosition (Program.runCall c p w).seed _ j).symm

theorem sampledEntry_predicate {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q) :
    entryPredicate (sampledEntryRequest hd w z j) =
      (Program.runCall c p w).pred z ((Program.runCall c p w).samples j) := by
  unfold entryPredicate
  rw [sampledEntry_position]
  rfl

theorem sampledEntry_mask {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q) :
    entryMask (sampledEntryRequest hd w z j) =
      decide ((Program.runCall c p w).pointMask z ((Program.runCall c p w).samples j) = 1) := by
  unfold entryMask
  rw [sampledEntry_position]
  rfl

end NearQuarticWires.StageMain
