import Proof.Quartic.StageNativeKids.Request
import Proof.Quartic.StagePrintTuple.RoleContext
import Proof.Quartic.StagePrintTuple.RoleMachine
import Proof.Quartic.StageNativeWidth.Polynomial
import Proof.Gates.Dispatch.ParamsF
import Proof.Gates.Dispatch.Print

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces
open StageTuple StagePrint.Header

/-- `sec:params` and `lem:print`, paper/paper.tex: the two complete original occurrence banks obey the
actual quartic census, independently of the selected role or child. -/
theorem original_count_bound (r : RowContext) :
    (Builder.allGates r.header.call).length ≤ 2 * r.header.call.n ^ 4 := by
  have h := r.header.prepared.input_valid.2.2.1.trans r.header.prepared.input_valid.2.2.2.1
  simpa only [Builder.callInput, Builder.allGates, List.length_append] using h

/-- `imp:partition` and `lem:print`, paper/paper.tex: the original affine translation is a finite canonical
binary code in at most the original number of coordinates. -/
theorem translation_lt (P : StarParams) (σ : P.Translation) :
    StagePullback.translationNumber P σ < 2 ^ P.n := by
  have hk : P.s * P.r ≤ P.n := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left P.r P.s_le_b).trans P.r_mul_b_le
  have h := (finFunctionFinEquiv (fun i : Fin P.r => finFunctionFinEquiv (σ i))).isLt
  change StagePullback.translationNumber P σ < (2 ^ P.s) ^ P.r at h
  rw [← pow_mul] at h
  exact h.trans_le (Nat.pow_le_pow_right (by decide) hk)

/-- `imp:partition`, `imp:seed` and `lem:print`, paper/paper.tex: the actual radix is positive
and has binary length controlled by the original dimension, rather
than requiring enumeration up to its numeric value. -/
theorem radix_bounds (r : RowContext) :
    0 < r.header.prepared.seedParameters.N ∧
      r.header.prepared.seedParameters.N ≤ 2 ^ r.header.call.n := by
  rw [r.header.prepared.seed_N, r.header.prepared.N_eq]
  refine ⟨Nat.two_pow_pos _, Nat.pow_le_pow_right (by decide) ?_⟩
  exact (Nat.div_le_self _ _).trans r.header.prepared.k_lt_n.le

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual retained affine-header scalar has a
fixed original-arity binary bound, including the original translation. -/
theorem header_bits (r : RowContext) :
    ∀ v ∈ baseHeaderValues r.header,
      natBitLength v ≤ 35 * (r.header.call.n + 1) ^ 4 := by
  let n := r.header.call.n
  let T := (n + 1) ^ 4
  let P := Builder.star r.header.call r.header.prepared
  have hT : 1 ≤ T := Nat.pow_pos (Nat.succ_pos _)
  have hnT : n + 1 ≤ T := Nat.le_self_pow (by decide) _
  have h2T : (n + 1) ^ 2 ≤ T := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hr : r.header.parameters.r ≤ n := by
    have h := P.four_r_le_n
    change 4 * r.header.parameters.r ≤ n at h
    omega
  have hb : r.header.parameters.b ≤ n := by
    have h := (Nat.le_mul_of_pos_left P.b P.r_pos).trans P.r_mul_b_le
    rwa [r.header.prepared.star_b] at h
  have hs : r.header.parameters.s ≤ n := by
    have h := P.s_le_b
    rw [r.header.prepared.star_s, r.header.prepared.star_b] at h
    exact h.trans hb
  have hwidth := StageNativeWidth.nativeFieldWidth_le r
  change r.nativeFieldWidth ≤ 16 * (n + 1) ^ 2 at hwidth
  have hlin : r.inputFieldWidth ≤ r.nativeFieldWidth := by
    unfold RowContext.nativeFieldWidth
    omega
  have hnb := NearCubicGates.Close.Dispatch.natBitLength_le_succ
  have htrans : natBitLength (StagePullback.translationNumber P
      (Builder.translation r.header.call r.header.prepared r.header.witness)) ≤ n + 1 :=
    NearCubicGates.Close.Dispatch.natBitLength_le_of_lt
      ((translation_lt P _).trans_le (Nat.pow_le_pow_right (by decide)
        (by change n ≤ n + 1; omega : P.n ≤ n + 1)))
      (by omega)
  intro v hv
  simp only [baseHeaderValues, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hnb n).trans (by change n + 1 ≤ 35 * T; omega)
  · change natBitLength r.inputFieldWidth ≤ 35 * T
    exact (hnb _).trans (by omega)
  · change natBitLength r.nativeFieldWidth ≤ 35 * T
    exact (hnb _).trans (by omega)
  · exact (hnb _).trans (by change r.header.parameters.r + 1 ≤ 35 * T; omega)
  · exact (hnb _).trans (by change r.header.parameters.b + 1 ≤ 35 * T; omega)
  · exact (hnb _).trans (by change r.header.parameters.s + 1 ≤ 35 * T; omega)
  · exact htrans.trans (by change n + 1 ≤ 35 * T; omega)

/-- `sec:walks`, `lem:print` and `prop:time`, paper/paper.tex: the complete canonical
walk ordinal is read in binary within a linear original-dimension bit
bound; no loop indexed by its potentially exponential value is needed. -/
theorem walk_bits (r : RowContext) :
    natBitLength r.walkCode.val ≤ 8 * r.header.call.n + 1 := by
  have hn := (radix_bounds r).2
  have hp : r.header.prepared.seedParameters.N ^ 8 ≤ 2 ^ (8 * r.header.call.n) := by
    calc
      _ ≤ (2 ^ r.header.call.n) ^ 8 := Nat.pow_le_pow_left hn 8
      _ = _ := by rw [← pow_mul, Nat.mul_comm r.header.call.n 8]
  have hl : r.walkCode.val < 2 ^ (8 * r.header.call.n + 1) :=
    r.walkCode.isLt.trans_le (hp.trans (Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ)) (by omega : 8 * r.header.call.n ≤ 8 * r.header.call.n + 1)))
  exact NearCubicGates.Close.Dispatch.natBitLength_le_of_lt hl (by omega)

/-- `lem:print` and `prop:time`, paper/paper.tex: every field of the actual original role packet has a
fixed original-arity binary bound, including both bank sizes, the
radix, complete walk code and atom selected from the original support. -/
theorem role_fields_bits (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    ∀ v ∈ (r.rolePacket i).values,
      natBitLength v ≤ 35 * (r.header.call.n + 1) ^ 4 := by
  let n := r.header.call.n
  let T := (n + 1) ^ 4
  have hT : 1 ≤ T := Nat.pow_pos (Nat.succ_pos _)
  have hnT : r.header.call.n + 1 ≤ T := Nat.le_self_pow (by decide) _
  have hn4 : r.header.call.n ^ 4 ≤ T := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hG := original_count_bound r
  have hGT : (Builder.allGates r.header.call).length ≤ 2 * T :=
    hG.trans (Nat.mul_le_mul_left 2 hn4)
  have hfirst : r.header.call.first.gates.length ≤ 2 * T := by
    simp only [Builder.allGates, List.length_append] at hGT
    omega
  have hsecond : r.header.call.second.gates.length ≤ 2 * T := by
    simp only [Builder.allGates, List.length_append] at hGT
    omega
  have hi : i.val < 34 * T := by
    have h := i.isLt
    omega
  have hrad : natBitLength r.header.prepared.seedParameters.N ≤ n + 1 :=
    NearCubicGates.Close.Dispatch.natBitLength_le_of_lt
      (((radix_bounds r).2).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))) (by omega)
  have hwalk := walk_bits r
  intro v hv
  change natBitLength v ≤ 35 * T
  unfold RolePacket.values at hv
  rw [r.rolePacket_scalars i] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact header_bits r v hv
  · change v ∈ [r.header.call.first.gates.length, r.header.call.second.gates.length,
      r.header.prepared.seedParameters.N, r.walkCode.val, i.val] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (by omega)
    · exact (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (by omega)
    · exact hrad.trans (by omega)
    · exact hwalk.trans (by omega)
    · exact (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (by omega)

end NearQuarticWires.StageNativeKids
