import Proof.Quartic.StageGreedyNativeData.Requests
import Proof.Quartic.StageNativeWidth.Polynomial
import Proof.Quartic.StageRecovery.ResidueFactor

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyNativeData

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic StagePrint

/-- `sec:params` and `prop:time`, paper/paper.tex: degree and prime-power bits are uniformly
polynomial in original arity, independently of raw target integers. -/
theorem degree_bits_bound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    let C:=(preparationCoefficient B1+1)^2
    let E:=2*(B1+12)
    StageLift.residueDegreeBound r.child.selected.1 r.prime ≤ C*(r.child.call.n+1)^E ∧
      natBitLength (r.prime^r.child.selected.1.e) ≤ C*(r.child.call.n+1)^E := by
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hadm:=(Program.dispatch_admitted r.child.dispatched).1
  have hb : 1 ≤ r.child.call.radius*(r.child.call.n : ℚ)^B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hscalar:=hs.scalar_preparation_bounds B1 hb
  have hp : r.prime ≤ preparationEnvelope B1 r.child.call.n := by
    have hm:=r.prime_mem
    change r.prime∈r.child.selected.1.primes at hm
    rw [hs.primes_eq,NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1.trans hscalar.P
  have hD : StageLift.residueDegreeBound r.child.selected.1 r.prime ≤
      preparationEnvelope B1 r.child.call.n :=
    (StageGreedyCollector.entry_degree_le
      (GreedyEntry.Request.mk r ⟨0,StageLiftSourceCost.walkCount_pos r⟩)).trans hscalar.Dmax
  have hbits:=StageRecovery.primePower_bits_envelope r.prime r.child.selected.1.e
    (preparationEnvelope B1 r.child.call.n) hp hscalar.e
  have hbase : 1 ≤ (r.child.call.n+1)^(B1+12) := Nat.one_le_pow _ _ (by omega)
  have hsum : preparationEnvelope B1 r.child.call.n+1 ≤
      (preparationCoefficient B1+1)*(r.child.call.n+1)^(B1+12) := by
    unfold preparationEnvelope
    nlinarith only [hbase]
  have hsq:=Nat.pow_le_pow_left hsum 2
  rw [mul_pow,←pow_mul] at hsq
  have hsmall : preparationEnvelope B1 r.child.call.n ≤
      (preparationEnvelope B1 r.child.call.n+1)^2 := by nlinarith
  constructor
  · exact hD.trans (hsmall.trans (by simpa only [Nat.mul_comm] using hsq))
  · exact hbits.trans (by simpa only [Nat.mul_comm] using hsq)

/-- `lem:print` and `prop:time`, paper/paper.tex: both actual native header widths and the
original prime-power bit length have a fixed arity polynomial bound. -/
theorem native_widths_bound (B1 B2 : ℕ) :
    ∃ C E : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      (nativeRequest r).table.matrix.p+(nativeRequest r).table.q+
        natBitLength (nativeRequest r).modulus ≤ C*(r.child.call.n+1)^E := by
  let C:=(preparationCoefficient B1+1)^2
  let E:=2*(B1+12)
  refine ⟨3000*(C+1)^2,2*E+6,?_⟩
  intro r
  let entry:=GreedyEntry.Request.mk r ⟨0,StageLiftSourceCost.walkCount_pos r⟩
  have hb:=degree_bits_bound r
  have hw:=StageNativeWidth.native_widths_polynomial entry.rowContext
    entry.degree entry.coefficientBits C E hb.1 hb.2
  have hbits : natBitLength (r.prime^r.child.selected.1.e) ≤ C*(r.child.call.n+1)^E := hb.2
  have hmono : (r.child.call.n+1)^E ≤ (r.child.call.n+1)^(2*E+6) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hcoeff : C ≤ 1000*(C+1)^2 := by nlinarith
  have hcb:=hbits.trans (Nat.mul_le_mul hcoeff hmono)
  have hp : (nativeRequest r).table.matrix.p=entry.termRequest.stackWidth+1 := by
    exact equalityStream_fieldWidth r
  rw [hp]
  change entry.termRequest.stackWidth+1+
    (PrimT.C4Geo.dRow (GreedyCollector.star r)+2*(entry.termRequest.stackWidth+1)+3)+
    natBitLength (r.prime^r.child.selected.1.e) ≤ _
  have hwp : entry.termRequest.stackWidth+1 ≤
      1000*(C+1)^2*(r.child.call.n+1)^(2*E+6) := hw.2.1
  have hwq : PrimT.C4Geo.dRow (GreedyCollector.star r)+2*(entry.termRequest.stackWidth+1)+3 ≤
      1000*(C+1)^2*(r.child.call.n+1)^(2*E+6) := hw.2.2
  nlinarith only [hwp,hwq,hcb]

end NearQuarticWires.StageGreedyNativeData
