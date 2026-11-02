import Proof.Quartic.StagePrint.GreedyEntryDock
import Proof.Quartic.StageLift.SourceEnvelope
import Proof.Quartic.StageLift.ResidueBounds
import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StagePrintContext.Cost
import Proof.Quartic.Control.GammaControl
import Proof.Quartic.StageGreedyEntryBounds.Lengths

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntryBounds

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Cells
open NearCubicGates.Close.Expand.Layout
open StagePrint StageLift

/-- `prop:time`, paper/paper.tex: the existing
actual original source envelope is used only as a mathematical bound. -/
noncomputable def entryEnvelope {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) : ℕ :=
  sourceEnvelope r.source

/-- `lem:print`, paper/paper.tex: the two
retained-source descriptions are the same literal dispatched preparation. -/
theorem prepared_word {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    r.prepared.word=preparedWordOf r.source := by
  change Program.prepWord B1 B2 r.source.child.call r.source.child.witness=_
  rw [StageMain.Compact.prepWord_eq_compact r.source.child.dispatched]
  rfl

/-- `sec:params` and `lem:print`, paper/paper.tex: all small per-entry headers are bounded from the actual
selected source; binary modulus and walk values enter only by bit length. -/
theorem entry_headers {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    2≤entryEnvelope r ∧ r.source.child.call.n+1≤entryEnvelope r ∧
    (Builder.allGates r.source.child.call).length≤entryEnvelope r ∧
    r.degree≤entryEnvelope r ∧
    natBitLength r.modulus≤(entryEnvelope r+1)^2 ∧
    natBitLength r.index.val≤4*entryEnvelope r+1 := by
  have he:=sourceEnvelope_bounds r.source
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hadm:=(Program.dispatch_admitted r.source.child.dispatched).1
  have hb : 1≤r.source.child.call.radius*(r.source.child.call.n:ℚ)^B1 :=
    hadm.2.2.2.2.2.2.2.2.2.1
  have hscalar:=hs.scalar_preparation_bounds B1 hb
  have hbase : Cells.ParameterArithmetic.preparationEnvelope B1 r.source.child.call.n≤entryEnvelope r := by
    unfold entryEnvelope sourceEnvelope
    omega
  have hn : r.source.child.call.n+1≤entryEnvelope r :=
    (Cells.ParameterArithmetic.preparation_envelope_arity _ _).trans hbase
  have hp : r.source.prime≤r.source.child.selected.1.P := by
    have hm:=r.source.prime_mem
    change r.source.prime∈r.source.child.selected.1.primes at hm
    rw [hs.primes_eq,NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1
  have hd : r.degree≤entryEnvelope r :=
    (residueDegreeBound_le_Dmax hs r.source.prime hp).trans (hscalar.Dmax.trans hbase)
  have hq:=StageCertTests.power_bitLength_le r.source.prime r.source.child.selected.1.e
  have hprime : natBitLength r.source.prime≤entryEnvelope r+1 :=
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (Nat.add_le_add_right he.prime 1)
  have hqbits : natBitLength r.modulus≤(entryEnvelope r+1)^2 := by
    have hh:=Nat.mul_le_mul he.exponent hprime
    change _≤entryEnvelope r*(entryEnvelope r+1) at hh
    change natBitLength (r.source.prime^r.source.child.selected.1.e)≤_
    nlinarith only [hq,hh]
  have hN : r.source.child.cellCall.seed.N=r.source.child.selected.1.N := hs.seed_N
  have hwalk : r.source.child.cellCall.seed.N^8≤2^(4*r.source.child.selected.1.k) := by
    rw [hN,hs.N_eq,←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    have hh:=Nat.div_mul_le_self r.source.child.selected.1.k 2
    omega
  have hi:=nbl_le_of_lt r.index.val _ (r.index.isLt.trans_le hwalk)
  exact ⟨he.positive,hn,he.occurrences,hd,hqbits,hi.trans (by
    have hh:=he.partition
    change r.source.child.selected.1.k≤entryEnvelope r at hh
    change _≤4*entryEnvelope r+1
    omega)⟩

/-- `lem:print`, paper/paper.tex: the actual
checked once-source context writer bounds the retained context bytes;
no context or byte-count supplier is assumed. -/
theorem context_length {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (EntryFormat.ofGreedy r).contextWord.length≤10^25*(entryEnvelope r+1)^8+1 := by
  have heq : (EntryFormat.ofGreedy r).contextWord=Context.word r.prepared := by
    simp only [EntryFormat.Request.contextWord,EntryFormat.Request.countsWord,
      EntryFormat.ofGreedy,GreedyEntry.Request.rowContext,Context.header,
      GreedyEntry.Request.prepared,Context.word,Context.countsWord,Context.geometryWord,
      Cells.ParameterRules.seed_N]
  have hout:=Control.output_length_le (StagePrintContext.contextProducer B1 B2).2 r.prepared
  have hbudget:=StagePrintContext.contextBudget_bound r.prepared
  have hprep : r.prepared.word.length≤entryEnvelope r := by
    rw [prepared_word]
    unfold entryEnvelope sourceEnvelope
    omega
  rw [heq]
  change (frame (Context.word r.prepared)).length≤StagePrintContext.contextBudget r.prepared+1 at hout
  rw [frame_length] at hout
  exact (by omega : (Context.word r.prepared).length≤StagePrintContext.contextBudget r.prepared+1).trans
    (Nat.add_le_add_right (hbudget.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.add_le_add_right hprep 1) _))) 1)

end NearQuarticWires.StageGreedyEntryBounds
