import Proof.Quartic.StagePrintTuple.RowFields
import Proof.Quartic.StagePrintTuple.WeightedTerms
import Proof.Gates.TabMachine.Stack2
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: the actual
original source and one canonical walk carry a distinct finite Terms
list with its explicit stacking width and degree. All additional fields
are mathematical bit/stack bounds, never supplied rows or pools. -/
structure TermCutRequest extends RowContext where
  terms : Terms (17 * (Builder.allGates header.call).length)
  stackWidth : ℕ
  degree : ℕ
  width_pos : 1 ≤ stackWidth
  terms_nodup : (Terms.keys terms).Nodup
  terms_degree : ∀ S ∈ Terms.keys terms, S.card ≤ degree
  row_width_le : toRowContext.nativeFieldWidth ≤ stackWidth + 1
  fields_fit : ∀ i, ∀ row ∈ toRowContext.nativeKids i, ∀ z ∈ row, encS z < 2 ^ (stackWidth + 1)
  coefficient_fit : ∀ t ∈ terms, encS t.2 < 2 ^ (stackWidth + 1)
  stack_fit : ∀ t ∈ terms, ∀ rows ∈ tuples ((t.1.sort (· ≤ ·)).map toRowContext.nativeKids),
    (magL rows + 1) ^ (t.1.card + 1) < 2 ^ stackWidth

/-- `lem:print`, paper/paper.tex: the actual
common two-half row dimension is fixed by the original prepared star. -/
def TermCutRequest.rowDimension (r : TermCutRequest) : ℕ :=
  2 * NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.header.prepared.starParams

/-- `lem:print`, paper/paper.tex: the literal
retained source context contains the real occurrence-bank counts, real
sampler radix and unchanged canonical walk ordinal. -/
def TermCutRequest.contextWord (r : TermCutRequest) : List Bool :=
  natWord r.header.call.first.gates.length ++ natWord r.header.call.second.gates.length ++
    natWord r.header.prepared.seedParameters.N ++ natWord r.walkCode.val

/-- `lem:print`, paper/paper.tex: the frozen
cold input consists of exactly eleven actual source fields; no child
pool, selected row, inferred output count or decoded header is an input. -/
def TermCutRequest.word (r : TermCutRequest) : List Bool :=
  Top.loadRec (frame (callWord r.header.call))
    (frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord))
    r.contextWord (termsWord r.terms) (natWord r.stackWidth) (natWord r.degree)
    [] [] [] [] []

/-- `lem:print`, paper/paper.tex: exact signed
equality records follow the literal monomial order and lexicographic
original-child tuple order, before any two-dominance conversion. -/
def TermCutRequest.output (r : TermCutRequest) : List Bool :=
  r.terms.flatMap fun t =>
    (tuples ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids)).flatMap
      (cutRecs r.stackWidth r.rowDimension t.2)

/-- `lem:print`, paper/paper.tex: an empty
Terms list produces exactly no equality records. -/
theorem TermCutRequest.output_of_nil (r : TermCutRequest) (ht : r.terms = []) : r.output = [] := by
  simp [TermCutRequest.output, ht]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual input's distinct monomial supports obey the
sharp weighted original-child square census at their real degree. -/
theorem TermCutRequest.weighted_census (r : TermCutRequest) (mc : ℕ) :
    (r.terms.map (fun t => mc ^ (2 * t.1.card))).sum ≤
      (1 + 17 * (Builder.allGates r.header.call).length * mc) ^ (2 * r.degree) :=
  weighted_terms_le r.terms r.degree mc r.terms_nodup r.terms_degree

end NearQuarticWires.StageTuple
