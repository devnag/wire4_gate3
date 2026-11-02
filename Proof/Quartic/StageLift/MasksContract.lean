import Proof.Quartic.StageLift.ResidueCacheContract
import Proof.Quartic.StageLift.SourceEnvelope
import Proof.Quartic.StageLift.SourceCarrier
import Proof.Quartic.StageCert.StructuralLoad
import Proof.Quartic.StageCert.CompleteWalkMasks

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `def:mask` and `lem:print`, paper/paper.tex: the actual shared structural query for one edge of
this original low-first walk, using the retained preparation source. -/
noncomputable def printMaskStructuralRequest {B1 B2 : ℕ}
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N ^ 8)) (edge : Fin 8) :
    StageMainMask.StructuralRequest B1 B2 where
  call := r.child.call
  selected := r.child.selected
  dispatched := r.child.dispatched
  witness := r.child.witness
  left := printWalkAt _ index (Cells.leftSlot (by decide : 0 < 4) edge)
  right := printWalkAt _ index (Cells.rightSlot (by decide : 0 < 4) edge)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the physically enumerated guarded-tuple
mask AST, retaining every original occurrence and structural factor. -/
noncomputable def printMasksFormula {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) : Formula (17 * (Builder.allGates r.child.call).length) :=
  let hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  Cells.walkMaskFormula (fun edge => StageCert.tupleMaskFormula
    (StagePrint.callStructural r.child.call hs (printWalkAt _ index) edge)
    (StagePrint.selectedSquare (by decide : 0 < 4)
      (Builder.selection r.child.call (p := r.child.selected.1) r.child.witness) edge)
    r.child.selected.1.tau r.child.selected.1.Xmax)

/-- `lem:print` and `prop:time`, paper/paper.tex: actual tuple enumeration retains its G^X construction
cost. Eight real structural calls, source copies and scalar reloads
are charged in addition; no polynomial-in-envelope claim is made. -/
noncomputable def printMasksCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (L B : ℕ) : ℕ :=
  let E := sourceEnvelope r
  StageCert.Tokens.completeMaskSourceCost (Builder.allGates r.child.call).length
    r.child.selected.1.k r.child.selected.1.Xmax (2 * (E + 1)) (4 * (E + 1))
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length +
    8 * (L + B + 9 * (preparedWordOf r).length + 80 * (E + 1) + 500) +
    10000 * (E + 1) ^ 4

/-- `lem:print`, paper/paper.tex: actual source
entry to the finite eight-mask producer. All data are existing retained
original bytes or already physically computed loop metadata. Structural
reservations bound the concrete shared cold callee, not a flag oracle. -/
structure PrintMasksReady {B1 B2 : ℕ} (width : ℕ) (input : List Bool) (L B : ℕ)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N ^ 8))
    (a : DS VV MM) : Prop where
  residue : ResidueReady (StageCert.Tokens.structuralSourceContext B1 B2 width input L B)
    r a (sourceEnvelope r)
  preparedRecords : a.ram preparedStore = (preparedWordOf r).map Bool.toNat
  preparedBytes : a.env preparedLength = (preparedWordOf r).length
  preparedCursor : a.rc preparedStore = (preparedWordOf r).length
  inputEmpty : a.kin = []
  walkOrdinal : a.env printWalkIndex = index.val
  sourceRoom : ∀ edge, (StageMainMask.structuralWord (printMaskStructuralRequest r index edge)).length ≤ L
  sourceBudget : ∀ edge, StageMainMask.structuralBudget (printMaskStructuralRequest r index edge) ≤ B

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact physical source for the eight original masks,
including actual StructuralCold calls and the preserved index/Gamma
sources. The callee reply tape may change as those calls really occur. -/
def printMasksProgramSpec (body : St VV MM) : Prop :=
  ∀ {B1 B2 : ℕ} (width : ℕ) (input : List Bool) (L B : ℕ)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N ^ 8))
    (a : DS VV MM) (_ready : PrintMasksReady width input L B r index a),
    let C := StageCert.Tokens.structuralSourceContext B1 B2 width input L B
    Hs C body a (printMasksCost r L B) (fun z =>
      z.out = a.out ++ (toks (printMasksFormula r index)).flatMap tokWord ∧
      z.ram = a.ram ∧
      (∀ store, store ∉ [parameterStore, witnessStore] → z.rc store = a.rc store) ∧
      z.ip = a.ip ∧ z.kin = [] ∧ ResidueReady C r z (sourceEnvelope r) ∧
      (∀ x ∈ ([54, 55, 56, 57, 58, 59, 60, 63, 71, 72, 76, 96, 127] : List (Fin VV)),
        z.env x = a.env x))

end NearQuarticWires.StageLift
