import Proof.Quartic.StagePrint.TermsCarrierTarget
import Proof.Quartic.StagePrint.ContextTarget
import Proof.Quartic.StageNativeWidth.Request

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.GreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator NearCubicGates.Close.Expand
open NearCubicGates.Close.Cells StageLift

/-- Step 3 and `lem:print`, paper/paper.tex: one actual compiled entry retains the complete
original print request and its original low-first walk ordinal. -/
structure Request (B1 B2 : ℕ) where
  source : Greedy.PrintRequest B1 B2
  index : Fin (source.child.cellCall.seed.N^8)

def Request.prepared {B1 B2 : ℕ} (r : Request B1 B2) : StageCertTests.PreparedScheduleRequest B1 B2 :=
  ⟨r.source.child.call,r.source.child.witness,r.source.child.selected,r.source.child.dispatched⟩

theorem Request.gate_bits {B1 B2 : ℕ} (r : Request B1 B2)
    (i : Fin (Builder.allGates r.source.child.call).length) :
    GateBits (Call.B0 r.source.child.call.n) (callAtoms r.source.child.call i) := by
  have ha:=(Program.dispatch_admitted r.source.child.dispatched).1
  have hi : callAtoms r.source.child.call i∈r.source.child.call.first.gates++r.source.child.call.second.gates :=
    List.getElem_mem i.isLt
  rcases List.mem_append.mp hi with hi|hi
  · exact ha.2.1.2.2.2 _ hi
  · exact ha.2.2.1.2.2.2 _ hi

/-- `lem:print`, paper/paper.tex:
the native row context is computed from actual source data, never
from an extra atom-map or original-gate-bound assumption. -/
def Request.rowContext {B1 B2 : ℕ} (r : Request B1 B2) : StageTuple.RowContext where
  header:=Context.header r.prepared
  walkCode:=r.index
  gate_bits:=r.gate_bits

noncomputable def Request.terms {B1 B2 : ℕ} (r : Request B1 B2) :=
  TermsCarrier.actualTerms r.source r.index
def Request.degree {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  residueDegreeBound r.source.child.selected.1 r.source.prime
def Request.modulus {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  r.source.prime^r.source.child.selected.1.e
def Request.coefficientBits {B1 B2 : ℕ} (r : Request B1 B2) : ℕ := natBitLength r.modulus

theorem Request.modulus_pos {B1 B2 : ℕ} (r : Request B1 B2) : 0<r.modulus :=
  lt_of_lt_of_le (by decide : 0<2) (Reconstruct.PrintRequest.two_le_modulus r.source)

theorem Request.keys_eq {B1 B2 : ℕ} (r : Request B1 B2) :
    Terms.keys r.terms=famS (17*(Builder.allGates r.source.child.call).length) r.degree := by
  simp [Request.terms,TermsCarrier.actualTerms,StageLift.sourceWalkPacket,
    StageRecovery.boundedModTerms,Terms.keys,List.map_map,Function.comp_def,Request.degree]

theorem Request.terms_nodup {B1 B2 : ℕ} (r : Request B1 B2) : (Terms.keys r.terms).Nodup := by
  rw [r.keys_eq]
  exact famS_nodup _ _

theorem Request.terms_degree {B1 B2 : ℕ} (r : Request B1 B2) :
    ∀ S∈Terms.keys r.terms,S.card≤r.degree := by
  rw [r.keys_eq]
  exact famS_card _ _

theorem Request.coefficient_bits {B1 B2 : ℕ} (r : Request B1 B2) :
    ∀ t∈r.terms,t.2.natAbs<2^r.coefficientBits := by
  intro t ht
  have h:=StageRecovery.boundedModTerms_bounds r.modulus r.modulus_pos
    (StageLift.reduceConstants r.modulus (StageLift.sourceWalkFormula r.source r.index)) r.degree t ht
  have ha : (t.2.natAbs : ℤ)<(r.modulus : ℤ) := by
    rw [←Int.abs_eq_natAbs,abs_of_nonneg h.1]
    exact h.2
  have hn : t.2.natAbs<r.modulus := by exact_mod_cast ha
  exact hn.trans (lt_natBitLength r.modulus)

/-- `lem:print`, paper/paper.tex: every actual
compiled Greedy entry supplies all existing sharp tuple-request
proofs at the arithmetic width computed from its real metadata. -/
noncomputable def Request.termRequest {B1 B2 : ℕ} (r : Request B1 B2) : StageTuple.TermCutRequest :=
  StageNativeWidth.termCutRequest r.rowContext r.terms r.degree r.coefficientBits
    r.terms_nodup r.terms_degree r.coefficient_bits

end NearQuarticWires.StagePrint.GreedyEntry
