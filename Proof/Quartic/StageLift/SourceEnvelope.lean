import Proof.Quartic.StageLift.CachedRequest
import Proof.Quartic.Cells.ParametersCertificateBits
import Proof.Quartic.Cells.ParametersPreparationWords

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: arithmetic workspace depends only on the original
selected source, before the Gamma and arbitrary index suffixes. -/
noncomputable def sourceEnvelope {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  preparationEnvelope B1 r.child.call.n + (preparedWordOf r).length + 2

/-- `lem:print` and `prop:time`, paper/paper.tex: bounds needed for the actual retained-source replays.
These are consequences of the original dispatched call, not fields
added to the runtime request. -/
structure SourceEnvelopeBounds {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (E : ℕ) : Prop where
  positive : 2 ≤ E
  occurrences : (Builder.allGates r.child.call).length ≤ E
  exponent : r.child.selected.1.e ≤ E
  chains : r.child.selected.1.J ≤ E
  partition : r.child.selected.1.k ≤ E
  prime : r.prime ≤ E
  M1 : r.child.selected.1.M1 ≤ 2 ^ E
  A : r.child.selected.1.A ≤ 2 ^ E
  factors : ∀ v ∈ r.child.selected.1.factors, v ≤ 2 ^ E
  witness : (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length ≤ (E + 1) ^ 3

/-- `sec:params` and `prop:time`, paper/paper.tex: every actual printer request supplies the common
source envelope through its existing dispatch and prime-membership
proofs, uniformly over all raw index integers. -/
theorem sourceEnvelope_bounds {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    SourceEnvelopeBounds r (sourceEnvelope r) := by
  let E := sourceEnvelope r
  let V := preparationEnvelope B1 r.child.call.n
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hadm := (Program.dispatch_admitted r.child.dispatched).1
  have hb : 1 ≤ r.child.call.radius * (r.child.call.n : ℚ) ^ B1 :=
    hadm.2.2.2.2.2.2.2.2.2.1
  have hscalar := hs.scalar_preparation_bounds B1 hb
  have hVE : V ≤ E := by dsimp [V, E, sourceEnvelope]; omega
  have hpow : V ≤ 2 ^ E := (Nat.lt_two_pow_self (n := V)).le.trans
    (Nat.pow_le_pow_right (by decide) hVE)
  have hn : r.child.call.n ≤ V :=
    (Nat.le_succ _).trans (preparation_envelope_arity B1 r.child.call.n)
  have hG : (Builder.allGates r.child.call).length ≤ V := by
    simpa only [Builder.callInput, Builder.allGates, List.length_append] using
      hs.occurrences_preparation_envelope B1
  have hprime : r.prime ≤ r.child.selected.1.P := by
    have hm := r.prime_mem
    change r.prime ∈ r.child.selected.1.primes at hm
    rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1
  have hw : (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length ≤
      (preparedWordOf r).length := by
    simp only [preparedWordOf, StageMain.Compact.compactInput, List.length_append,
      RepairOrdinary.frame_length]
    omega
  have hwE : (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length ≤ E := by
    dsimp [E, sourceEnvelope]
    omega
  refine ⟨by dsimp [E, sourceEnvelope]; omega, hG.trans hVE,
    hscalar.e.trans hVE, hscalar.J.trans hVE, hscalar.k.trans hVE,
    hprime.trans (hscalar.P.trans hVE), hscalar.M1.trans hpow,
    hscalar.A.trans hpow, ?_, ?_⟩
  · intro v hv
    exact (hs.factor_member_preparation_bound v hv).trans (hn.trans hpow)
  · exact hwE.trans ((Nat.le_succ _).trans (Nat.le_self_pow (by decide) _))

end NearQuarticWires.StageLift
