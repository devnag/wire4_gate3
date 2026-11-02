import Proof.Quartic.StagePrint.GreedyEntryData

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.EntryFormat

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the same
literal source context and Terms field support exact coefficients
or coefficients reduced modulo an actual binary scale. -/
structure Request (modular : Bool) extends StageTuple.RowContext where
  terms : Terms (17*(Builder.allGates header.call).length)
  degree : ℕ
  scale : ℕ
  terms_nodup : (Terms.keys terms).Nodup
  terms_degree : ∀ S∈Terms.keys terms,S.card≤degree
  coefficient_bits : ∀ t∈terms,t.2.natAbs<2^(if modular then natBitLength scale else scale)

/-- `lem:print`, paper/paper.tex: exact mode
uses its physically written coefficient-bit bound; modular mode derives
that bound from its physically written arithmetic modulus. -/
def Request.coefficientBits {modular : Bool} (r : Request modular) : ℕ :=
  if modular then natBitLength r.scale else r.scale

/-- `lem:print`, paper/paper.tex: all existing
row, coefficient and radix-fit obligations are discharged from the
actual finite Terms data, with no extra physical source fields. -/
def Request.termRequest {modular : Bool} (r : Request modular) : StageTuple.TermCutRequest :=
  StageNativeWidth.termCutRequest r.toRowContext r.terms r.degree r.coefficientBits
    r.terms_nodup r.terms_degree r.coefficient_bits

/-- `lem:print`, paper/paper.tex:
the three count fields omit only the walk ordinal appended later. -/
def Request.countsWord {modular : Bool} (r : Request modular) : List Bool :=
  [r.header.call.first.gates.length,r.header.call.second.gates.length,
    r.header.prepared.seedParameters.N].flatMap natWord

/-- `lem:print`, paper/paper.tex: the retained
context contains actual original bytes, common affine-header bytes,
occurrence counts and four original star scalars, never a child pool. -/
def Request.contextWord {modular : Bool} (r : Request modular) : List Bool :=
  Top.loadRec (frame (callWord r.header.call))
    (frame ((Header.baseHeaderValues r.header).flatMap natWord))
    r.countsWord
    ([r.header.call.n,r.header.parameters.r,r.header.parameters.b,r.header.parameters.s].flatMap natWord)
    [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the leading
original arity controls the machine's word width; neither the Terms
length nor a possibly large walk value determines that width. -/
def Request.word {modular : Bool} (r : Request modular) : List Bool :=
  natWord r.header.call.n ++ r.contextWord ++ natWord r.walkCode.val ++
    natWord r.degree ++ natWord r.scale ++ frame (termsWord r.terms)

/-- `lem:print`, paper/paper.tex: the actual
Greedy entry specializes the shared formatter without changing any
source, walk ordinal, coefficient, degree or original occurrence. -/
noncomputable def ofGreedy {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) : Request true where
  toRowContext:=r.rowContext
  terms:=r.terms
  degree:=r.degree
  scale:=r.modulus
  terms_nodup:=r.terms_nodup
  terms_degree:=r.terms_degree
  coefficient_bits:=r.coefficient_bits

end NearQuarticWires.StagePrint.EntryFormat
