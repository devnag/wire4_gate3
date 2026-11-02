import Proof.Quartic.StageCert.MomentBody
import Proof.Quartic.Cells.ParametersCertificateBits

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open Cells.ParameterArithmetic

/-- `sec:params`, paper/paper.tex: successful
dispatch supplies the actual lower radius guard of the original call. -/
theorem MomentRequest.radius_lower {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    1≤(Builder.callInput r.call).beta*((Builder.callInput r.call).n:ℚ)^B1 :=
  (Program.dispatch_admitted r.dispatched).1.2.2.2.2.2.2.2.2.2.1

/-- `sec:params` and `prop:time`, paper/paper.tex: all selected scalar values have their proved original
arity envelope, on every retained proposed witness. -/
theorem MomentRequest.scalar_bounds {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Cells.ScalarPreparationBounds B1 (Builder.callInput r.call) r.selected.1 :=
  r.rules.scalar_preparation_bounds B1 r.radius_lower

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual low-first ordinal needs at most 4k+1
bits, for the exact N² population or N⁸ walk census. -/
theorem MomentRequest.index_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    natBitLength r.index.val≤4*r.selected.1.k+1 := by
  have hN : 1≤r.selected.1.N := (Cells.ParameterRules.N_ge_two r.rules).trans' (by decide)
  have hcount : momentTermCount r.selected.1.N r.test≤r.selected.1.N^8 := by
    cases r.test with
    | population => exact Nat.pow_le_pow_right hN (by decide : 2≤8)
    | digit _ _ _ => exact le_rfl
    | finalError _ _ => exact le_rfl
  have hi : r.index.val<r.selected.1.N^8 := r.index.isLt.trans_le hcount
  have hpow : r.selected.1.N^8≤2^(4*r.selected.1.k) := by
    rw [r.rules.N_eq,←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hb := StageLift.codec_nbl_mono ((hi.trans_le hpow).le)
  have hp : natBitLength (2^(4*r.selected.1.k))=4*r.selected.1.k+1 := by
    unfold natBitLength
    rw [Nat.log_pow (by decide : 1<(2:ℕ))]
  rw [hp] at hb
  exact hb

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: every literal strict-test threshold
has the proved common certificate bit envelope before any column passes. -/
theorem MomentRequest.threshold_bound {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (r.test.metadata r.selected.1).threshold≤
      2^certificateBitEnvelope (preparationEnvelope B1 r.call.n) := by
  have hh := r.rules.selected_other_moment_power_bounds B1 r.radius_lower
  cases r.test with
  | population => exact hh.2.1
  | digit _ _ _ => exact hh.2.2.1
  | finalError _ _ => exact hh.2.2.2

/-- `lem:print` and `prop:time`, paper/paper.tex: all six parsed original source fields have an explicit
original-arity bit bound, including full threshold and ordinal words. -/
theorem MomentRequest.source_bits_envelope {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    ∀v∈r.sourceValues,natBitLength v≤
      certificateBitEnvelope (preparationEnvelope B1 r.call.n)+
        4*preparationEnvelope B1 r.call.n+260 := by
  let V := preparationEnvelope B1 r.call.n
  let K := certificateBitEnvelope V
  have hs := r.scalar_bounds
  have htag : (r.test.metadata r.selected.1).tag≤2 := by
    cases r.test <;> norm_num [StageCertTests.TestOrdinal.metadata]
  have hj : (r.test.metadata r.selected.1).circuit≤1 := by
    cases r.test with
    | population => norm_num [StageCertTests.TestOrdinal.metadata]
    | digit j _ _ => exact Nat.le_of_lt_succ j.isLt
    | finalError j _ => exact Nat.le_of_lt_succ j.isLt
  have hcode : (r.test.metadata r.selected.1).signOrdinal≤255 := by
    cases r.test with
    | population => norm_num [StageCertTests.TestOrdinal.metadata]
    | digit _ code _ => exact Nat.le_of_lt_succ code.isLt
    | finalError _ code => exact Nat.le_of_lt_succ code.isLt
  have hrow : (r.test.metadata r.selected.1).digitOrdinal≤r.selected.1.J := by
    cases r.test with
    | population => exact Nat.zero_le _
    | digit _ _ row => have hh := row.isLt; change row.val≤r.selected.1.J; omega
    | finalError _ _ => exact Nat.zero_le _
  have hlog (v : ℕ) : natBitLength v≤v+1 := by
    unfold natBitLength
    have hh := Nat.log_le_self 2 v
    omega
  have hth := StageLift.codec_nbl_mono r.threshold_bound
  have hp : natBitLength (2^K)=K+1 := by
    unfold natBitLength
    rw [Nat.log_pow (by decide : 1<(2:ℕ))]
  change natBitLength (r.test.metadata r.selected.1).threshold≤natBitLength (2^K) at hth
  rw [hp] at hth
  intro v hv
  simp only [MomentRequest.sourceValues,List.mem_cons,List.not_mem_nil,or_false] at hv
  have hJ : r.selected.1.J≤V := hs.J
  have hk : r.selected.1.k≤V := hs.k
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
  · have hh := hlog (r.test.metadata r.selected.1).tag
    change _≤K+4*V+260
    omega
  · have hh := hlog (r.test.metadata r.selected.1).circuit
    change _≤K+4*V+260
    omega
  · have hh := hlog (r.test.metadata r.selected.1).signOrdinal
    change _≤K+4*V+260
    omega
  · have hh := hlog (r.test.metadata r.selected.1).digitOrdinal
    change _≤K+4*V+260
    omega
  · change _≤K+4*V+260
    omega
  · have hh := r.index_bits
    change _≤K+4*V+260
    omega

end NearQuarticWires.StageCert.Tokens
