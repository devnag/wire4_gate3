import Proof.Quartic.StageGreedyEntryBounds.Source
import Proof.Quartic.StageGreedyEntryBounds.Sizing

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntryBounds

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint StageLift

/-- `sec:params` and `prop:time`, paper/paper.tex: the actual original source envelope has one fixed
arity polynomial, uniformly over every selected prime and witness. -/
theorem entryEnvelope_polynomial (B1 B2 : ℕ) : ∃C E : ℕ,
    ∀r : GreedyEntry.Request B1 B2,entryEnvelope r+1≤C*(r.source.child.call.n+1)^E := by
  let E:=B1+12+StageMain.Compact.capacityExponent B1 B2
  let C:=Cells.ParameterArithmetic.preparationCoefficient B1+
    StageMain.Compact.capacityCoefficient B1+3
  refine ⟨C,E,fun r=>?_⟩
  have hprep:=StageMain.Compact.compactInput_length_arity r.source.child.dispatched r.source.child.witness
  change (preparedWordOf r.source).length≤StageMain.Compact.capacityCoefficient B1*
    (r.source.child.call.n+1)^StageMain.Compact.capacityExponent B1 B2 at hprep
  have hn : 1≤r.source.child.call.n+1 := by omega
  have hpow0 : 1≤(r.source.child.call.n+1)^E := Nat.one_le_pow _ _ hn
  have hpow1 : (r.source.child.call.n+1)^(B1+12)≤(r.source.child.call.n+1)^E :=
    Nat.pow_le_pow_right hn (by dsimp [E];omega)
  have hpow2 : (r.source.child.call.n+1)^StageMain.Compact.capacityExponent B1 B2≤
      (r.source.child.call.n+1)^E := Nat.pow_le_pow_right hn (by dsimp [E];omega)
  have h1:=Nat.mul_le_mul_left (Cells.ParameterArithmetic.preparationCoefficient B1) hpow1
  have h2:=Nat.mul_le_mul_left (StageMain.Compact.capacityCoefficient B1) hpow2
  unfold entryEnvelope sourceEnvelope Cells.ParameterArithmetic.preparationEnvelope
  dsimp only [C]
  nlinarith only [hprep,hpow0,h1,h2]

/-- `lem:print`, paper/paper.tex: every actual
compiled Greedy entry satisfies the small allocator sizing bound,
including all zero-coefficient records in its original Terms word. -/
theorem sizingMagnitude_ofGreedy_envelope {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (EntryFormat.ofGreedy r).sizingMagnitude≤10^28*(entryEnvelope r+1)^8 := by
  obtain ⟨hpos,hn,hg,hd,hq,hi⟩:=entry_headers r
  exact sizingMagnitude_bound (EntryFormat.ofGreedy r) (entryEnvelope r+1)
    (by omega) (hn.trans (by omega)) (hg.trans (by omega)) (hd.trans (by omega))
    hq (by exact hi.trans (by omega)) (context_length r)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual unchanged Greedy entry allocator is bounded
by a fixed polynomial in the original call arity. No source, guard,
Terms byte count, Formula weight, or provider premise is added. -/
theorem sizingMagnitude_ofGreedy_polynomial (B1 B2 : ℕ) : ∃C E : ℕ,
    ∀r : GreedyEntry.Request B1 B2,
      (EntryFormat.ofGreedy r).sizingMagnitude≤C*(r.source.child.call.n+1)^E := by
  obtain ⟨C,E,he⟩:=entryEnvelope_polynomial B1 B2
  refine ⟨10^28*C^8,E*8,fun r=>?_⟩
  calc
    _≤10^28*(entryEnvelope r+1)^8 := sizingMagnitude_ofGreedy_envelope r
    _≤10^28*(C*(r.source.child.call.n+1)^E)^8 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (he r) _)
    _=_ := by rw [mul_pow,←pow_mul];ring

end NearQuarticWires.StageGreedyEntryBounds
