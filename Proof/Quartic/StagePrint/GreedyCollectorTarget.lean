import Proof.Quartic.StagePrint.GreedyEntryData
import Proof.Quartic.StagePrint.NativeEquations
import Proof.Quartic.StagePrint.DownstreamTargets
import Proof.Quartic.StagePrint.DenseWidth

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.GreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- Step 3 and `lem:print`, paper/paper.tex: the once-retained preparation is the original one
shared by every actual compiled walk entry. -/
def prepared {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    StageCertTests.PreparedScheduleRequest B1 B2 :=
  ⟨r.child.call,r.child.witness,r.child.selected,r.child.dispatched⟩

def star {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :=
  (Context.header (prepared r)).prepared.starParams

/-- `lem:print`, paper/paper.tex: a single
physical field width is fixed before all walk entries; the coefficient
modulus and native signed-field width remain distinct quantities. -/
def fieldWidth {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  NativeWidth.packedBits
    ((4*r.child.call.n+1)*Nat.clog 2 (r.child.call.n+1)+5+r.child.call.n+6)
    (2*PrimT.C4Geo.width (star r))
    (StageLift.residueDegreeBound r.child.selected.1 r.prime)
    (natBitLength (r.prime^r.child.selected.1.e))+1

/-- `lem:print`, paper/paper.tex: every actual
walk is expanded at its original small atom count, split into its two
weak predicates and only then reduced modulo the recovery modulus. -/
noncomputable def walkCuts {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (i : Fin (r.child.cellCall.seed.N^8)) : List MatrixScoreBatch.Cut :=
  (EquationRow.doubled false (nativeEqualityCuts (GreedyEntry.Request.termRequest ⟨r,i⟩))).map
    (StageRecovery.reduceCut (r.prime^r.child.selected.1.e))

/-- `lem:print`, paper/paper.tex: one stream
concatenates actual low-first walk entries, preserving all zero
coefficients and their original within-walk order. -/
noncomputable def stream {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  (List.ofFn fun i : Fin (r.child.cellCall.seed.N^8) =>
    (walkCuts r i).flatMap (MatrixScoreBatch.cutWord (fieldWidth r))).flatten

/-- `lem:print`, paper/paper.tex: the only
final native header input is five actual scalar fields followed by the
combined weak stream; no cut count, columns or table is supplied. -/
noncomputable def word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  [(star r).n,(star r).r,(star r).b,(star r).s,fieldWidth r].flatMap natWord++stream r

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: the whole collector starts
with the once-context compiled carrier and physically produces the
one common native input, with its actual selected clock. -/
abbrev Producer (B1 B2 : ℕ) :=
  (budget : Greedy.PrintRequest B1 B2→ℕ) ×
    WordFunction (Greedy.PrintRequest B1 B2) TermsCarrier.word (fun r=>frame (word r)) budget

end NearQuarticWires.StagePrint.GreedyCollector
