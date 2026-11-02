import Proof.Quartic.StageNativeKids.RoleBridge

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageTuple StagePrint.Header

/-- `lem:print` and `prop:time`, paper/paper.tex: the output original index, retained scalar
header and two selected walk vertices all fit the same arity workspace. -/
theorem role_output_bits (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    ∀ v ∈ (r.rolePacket i).outputValues,
      natBitLength v ≤ 35 * (r.header.call.n + 1) ^ 4 := by
  let T := (r.header.call.n + 1) ^ 4
  have hnT : r.header.call.n + 1 ≤ T := Nat.le_self_pow (by decide) _
  have hn4 : r.header.call.n ^ 4 ≤ T := Nat.pow_le_pow_left (Nat.le_succ _) _
  have hG : (Builder.allGates r.header.call).length ≤ 2 * T :=
    (original_count_bound r).trans (Nat.mul_le_mul_left 2 hn4)
  have hi : (r.originalIndex i).val < 2 * T := (r.originalIndex i).isLt.trans_le hG
  have hN := radix_bounds r
  have digitBits (a : ℕ) : natBitLength (a % r.header.prepared.seedParameters.N) ≤
      r.header.call.n + 1 := by
    apply NearCubicGates.Close.Dispatch.natBitLength_le_of_lt _ (by omega)
    exact (Nat.mod_lt _ hN.1).trans_le (hN.2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
  intro v hv
  change natBitLength v ≤ 35 * T
  simp only [RolePacket.outputValues, role_originalIndex,
    List.mem_cons, List.mem_append, r.rolePacket_scalars i,
    List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | hv) | rfl | rfl
  · exact (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (by omega)
  · exact header_bits r v hv
  · exact (digitBits _).trans (by omega)
  · exact (digitBits _).trans (by omega)

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual atom source gives a valid
role-machine request. These are derived finite bit bounds, rather than
a supplied occurrence, row, child pool or decoded role. -/
def actualRoleRequest (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) : RoleRequest where
  packet := r.rolePacket i
  fields_fit := by
    intro v hv
    rw [role_width]
    have h := role_fields_bits r i v hv
    have hp : 1 ≤ (r.header.call.n + 1) ^ 4 := Nat.pow_pos (by omega)
    omega
  radix_pos := (radix_bounds r).1
  banks_fit := by
    rw [role_width]
    have hG := original_count_bound r
    simp only [Builder.allGates, List.length_append] at hG
    change 2 * (r.header.call.first.gates.length + r.header.call.second.gates.length) ≤ _
    have hn : r.header.call.n ^ 4 ≤ (r.header.call.n + 1) ^ 4 :=
      Nat.pow_le_pow_left (Nat.le_succ _) _
    have he : 64 * (r.header.call.n + 1) ^ 4 < 2 ^ (64 * (r.header.call.n + 1) ^ 4) :=
      Nat.lt_two_pow_self
    omega
  radix_fit := by
    rw [role_width]
    change 2 * r.header.prepared.seedParameters.N ≤ _
    have hN := (radix_bounds r).2
    have hn : r.header.call.n + 1 ≤ (r.header.call.n + 1) ^ 4 :=
      Nat.le_self_pow (by decide) _
    calc
      _ ≤ 2 * 2 ^ r.header.call.n := Nat.mul_le_mul_left 2 hN
      _ = 2 ^ (r.header.call.n + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  output_fit := by
    intro v hv
    rw [role_width]
    have h := role_output_bits r i v hv
    have hp : 1 ≤ (r.header.call.n + 1) ^ 4 := Nat.pow_pos (by omega)
    exact (show natBitLength v + 2 ≤ 64 * (r.header.call.n + 1) ^ 4 by omega).trans_lt
      Nat.lt_two_pow_self

/-- `lem:print`, paper/paper.tex: the
proved role validity fields do not change any actual source byte. -/
theorem actualRoleRequest_word (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (actualRoleRequest r i).word = (r.rolePacket i).word := rfl

/-- `lem:print`, paper/paper.tex: the
actual role word function computes the exact original occurrence and
child-independent row header from the derived valid original source. -/
noncomputable def actualRoleWordFunction :
    WordFunction NativeKidsRequest
      (fun r => (r.toRowContext.rolePacket r.atom).word)
      (fun r => natWord (r.toRowContext.originalIndex r.atom).val ++
        r.toRowContext.rowHeader r.atom)
      (fun r => (actualRoleRequest r.toRowContext r.atom).budget) :=
  ⟨roleWordFunction.program, by
    intro r
    simpa only [RoleRequest.word, actualRoleRequest,
      role_output] using roleWordFunction.realizes (actualRoleRequest r.toRowContext r.atom)⟩

end NearQuarticWires.StageNativeKids
