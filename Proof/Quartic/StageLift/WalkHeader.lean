import Proof.Quartic.StageLift.WalkHead
import Proof.Quartic.StageLift.RawHeader

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: actual computed
metadata supply the raw packet's four scalar fields; arbitrary raw
index magnitudes enter none of their binary-width bounds. -/
theorem emitSelectedWalkHeader_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (a : DS VV MM)
    (ha : WalkSourceState C r index.val a) (hi : a.env printWalkIndex = index.val)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    Hs C emitRawWalkHeader a (1600 * (sourceEnvelope r + 1) ^ 2 + 173) (fun z =>
      z.out = a.out ++ natWord index.val ++ natWord (residueDegreeBound r.child.selected.1 r.prime) ++
        natWord (r.prime ^ r.child.selected.1.e) ++ natWord (17 * (Builder.allGates r.child.call).length) ∧
      WalkSourceState C r index.val z ∧ z.env printWalkIndex = index.val ∧ z.ip = a.ip) := by
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hadm := (Program.dispatch_admitted r.child.dispatched).1
  have hb : 1 ≤ r.child.call.radius * (r.child.call.n : ℚ) ^ B1 :=
    hadm.2.2.2.2.2.2.2.2.2.1
  have hscalar := hs.scalar_preparation_bounds B1 hb
  have hE : Cells.ParameterArithmetic.preparationEnvelope B1 r.child.call.n ≤ sourceEnvelope r := by
    dsimp [sourceEnvelope]
    omega
  have hprime : r.prime ≤ r.child.selected.1.P := by
    have hm : r.prime ∈ r.child.selected.1.primes := r.prime_mem
    rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1
  have hD : residueDegreeBound r.child.selected.1 r.prime ≤ sourceEnvelope r :=
    (residueDegreeBound_le_Dmax hs r.prime hprime).trans (hscalar.Dmax.trans hE)
  have hV : 17 * (Builder.allGates r.child.call).length ≤ sourceEnvelope r :=
    (StageRecovery.selected_occurrence_envelope r.child.call hs B1 hb).trans hE
  have hq := StageRecovery.primePower_bits_envelope r.prime r.child.selected.1.e (sourceEnvelope r)
    (sourceEnvelope_bounds r).prime (sourceEnvelope_bounds r).exponent
  have hN := source_walk_counter_bits r
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hbits : ∀ x ∈ rawHeaderFields, natBitLength (a.env x) ≤ 10 * (sourceEnvelope r + 1) ^ 2 := by
    intro x hx
    rcases (by simpa only [rawHeaderFields, List.mem_cons, List.not_mem_nil, or_false] using hx) with
      rfl | rfl | rfl | rfl
    · rw [hi]
      have h := codec_nbl_mono index.isLt.le
      omega
    · have h : a.env degreeVar = residueDegreeBound r.child.selected.1 r.prime := ha.sources.degree
      rw [h]
      have hn := nbl_le_self (residueDegreeBound r.child.selected.1 r.prime)
      omega
    · have h : a.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e := ha.sources.modulus
      rw [h]
      omega
    · have h : a.env printArityVar = 17 * (Builder.allGates r.child.call).length := ha.sources.arity
      rw [h]
      have hn := nbl_le_self (17 * (Builder.allGates r.child.call).length)
      omega
  have hcount : r.child.cellCall.seed.N ^ 8 < 2 ^ C.Wd :=
    (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hv := ha.valid (by rw [hi]; exact index.isLt.trans hcount)
  have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hd := StagePrint.source_addValid (by omega : 1 ≤ C.Wd) hv
    (emitRawWalkHeader_spec C a ha.constants (10 * (sourceEnvelope r + 1) ^ 2) hbits (by omega) (by omega))
  obtain ⟨z, n, he, hn, ⟨hzo, hzrest, hzc, hzfr⟩, hzvalid⟩ := hd
  have hzram : z.ram = a.ram := congrArg (fun t => t.2.1) hzrest
  have hzrc : z.rc = a.rc := congrArg (fun t => t.2.2.1) hzrest
  have hzkin : z.kin = [] :=
    (congrArg (fun t => t.2.2.2.1) hzrest).trans ha.inputEmpty
  have hzfields : ∀ x ∈ sourceHeaderRegisters, z.env x = a.env x := by
    have hdis : ∀ x : Fin VV, x ∈ sourceHeaderRegisters → x ∉ tokenScratch := by decide
    intro x hx
    exact hzfr _ (hdis x hx)
  have hzstate := ha.of_frame hzram hzfields (by rw [hzrc]; exact ha.gammaCursor)
    (by rw [hzrc]) hzc hzvalid hzkin
  refine ⟨z,n,he,by omega,?_,hzstate,(hzfr _ (by decide)).trans hi,
    congrArg (fun t => t.1) hzrest⟩
  have haD : a.env degreeVar = residueDegreeBound r.child.selected.1 r.prime := ha.sources.degree
  have haq : a.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e := ha.sources.modulus
  have haV : a.env printArityVar = 17 * (Builder.allGates r.child.call).length := ha.sources.arity
  simpa only [hi, haD, haq, haV] using hzo

end NearQuarticWires.StageLift
