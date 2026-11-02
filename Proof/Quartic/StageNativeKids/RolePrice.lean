import Proof.Quartic.StageNativeKids.SourceBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Cells
open StageTuple StagePrint StagePrint.Header StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: a fixed
list of actual natural header fields has an emission cost linear in its
cardinality and its proved bit bound, independent of their numeric values. -/
theorem native_header_emit_bound (values : List ℕ) (B : ℕ)
    (hb : ∀ v ∈ values, natBitLength v ≤ B) :
    headerEmitCost values ≤ values.length * (40 * B + 43) + 1 := by
  have hsum : (values.map (fun v => 40 * natBitLength v + 43)).sum ≤
      values.length * (40 * B + 43) := by
    induction values with
    | nil => simp
    | cons v vs ih =>
      have hv := hb v (by simp)
      have ht := ih (fun x hx => hb x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith only [hv, ht]
  unfold headerEmitCost
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual role parser, arithmetic and
header emitter have a fixed original-arity clock, even when the binary
radix, translation and complete walk ordinal have exponential magnitude. -/
theorem native_role_steps (r : NativeKidsRequest) :
    (r.toRowContext.rolePacket r.atom).steps ≤ 100000 * (r.header.call.n + 1)^4 := by
  have hi := StageGamma.readFieldsCost_le (r.toRowContext.rolePacket r.atom).values
    (35 * (r.header.call.n + 1)^4) (role_fields_bits r.toRowContext r.atom)
  have ho := native_header_emit_bound (r.toRowContext.rolePacket r.atom).outputValues
    (35 * (r.header.call.n + 1)^4) (role_output_bits r.toRowContext r.atom)
  have hil : (r.toRowContext.rolePacket r.atom).values.length = 12 := by
    simp [RolePacket.values]
  have hol : (r.toRowContext.rolePacket r.atom).outputValues.length = 10 := by
    simp [RolePacket.outputValues]
  rw [hil] at hi
  rw [hol] at ho
  have hp : 1 ≤ (r.header.call.n + 1)^4 := Nat.one_le_pow _ _ (by omega)
  unfold RolePacket.steps
  omega

/-- `lem:print`, paper/paper.tex: the
actual role source begins with its original arity codec, so ordinary
compiler workspace depends on original arity rather than walk magnitude. -/
theorem native_role_lead (r : NativeKidsRequest) :
    leadOnes (actualRoleRequest r.toRowContext r.atom).word = natBitLength r.header.call.n := by
  have hw := r.toRowContext.rolePacket_word r.atom
  change leadOnes (r.toRowContext.rolePacket r.atom).word = _
  rw [hw]
  unfold baseHeaderValues
  simp only [List.flatMap_cons]
  rw [List.append_assoc, List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

/-- `prop:time`, paper/paper.tex: all
actual role source bytes are literal subfields of the original source. -/
theorem native_role_word_le (r : NativeKidsRequest) :
    (r.toRowContext.rolePacket r.atom).word.length ≤ r.word.length := by
  have h := native_word_length r
  rw [r.toRowContext.rolePacket_word r.atom]
  change ((baseHeaderValues r.header).flatMap natWord ++ r.contextWord ++
    natWord r.atom.val).length ≤ _
  simp only [List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: the
fixed fourth-power source workspace gives a structural polynomial
bound for the ordinary role compiler's exact constant factor. -/
theorem native_role_gof_price : Price NativeKidsRequest.structuralScale
    (fun r => NearCubicGates.Close.CellsPack.Gof StageRecovery.packetCallee roleSizes
      (leadOnes (actualRoleRequest r.toRowContext r.atom).word)) := by
  have hn := native_arity_price
  have hnbit : Price NativeKidsRequest.structuralScale (fun r => natBitLength r.header.call.n) := by
    have h : Price NativeKidsRequest.structuralScale (fun r => r.header.call.n + 1) := by
      price_with structuralScale_pos
    exact h.mono fun r => NearCubicGates.Close.Dispatch.natBitLength_le_succ _
  have hpow : Price NativeKidsRequest.structuralScale
      (fun r => 2 ^ (4 * natBitLength r.header.call.n)) := by
    have h : Price NativeKidsRequest.structuralScale (fun r => 16 * (r.header.call.n + 1)^4) := by
      price_with structuralScale_pos
    apply h.mono
    intro r
    have hp := Nat.pow_le_pow_left
      (NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.header.call.n) 4
    rw [← pow_mul, Nat.mul_comm (natBitLength r.header.call.n) 4] at hp
    simpa only [mul_pow, show (2 : ℕ) ^ 4 = 16 from rfl] using hp
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      1000 * (2 ^ (4 * natBitLength r.header.call.n) + natBitLength r.header.call.n +
        TSK StageRecovery.packetCallee + 1)) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  rw [native_role_lead]
  simp only [NearCubicGates.Close.CellsPack.Gof, roleSizes, Sz.W, Sz.Lk, Sz.Bk,
    Nat.zero_mul, pow_zero, Nat.mul_zero, Nat.add_zero]
  omega

/-- `prop:time`, paper/paper.tex: the
complete actual framed role machine has an unconditional structural
polynomial budget, including physical ordinary simulation and output. -/
theorem native_role_budget_price : Price NativeKidsRequest.structuralScale framedRoleBudget := by
  have hn := native_arity_price
  have hg := native_role_gof_price
  have hi : Price NativeKidsRequest.structuralScale
      (fun r => (actualRoleRequest r.toRowContext r.atom).word.length) :=
    native_word_price.mono fun r => native_role_word_le r
  have hs : Price NativeKidsRequest.structuralScale
      (fun r => (r.toRowContext.rolePacket r.atom).steps) := by
    have h : Price NativeKidsRequest.structuralScale (fun r => 100000 * (r.header.call.n + 1)^4) := by
      price_with structuralScale_pos
    exact h.mono native_role_steps
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      10 ^ 6 * ((3 * ((r.toRowContext.rolePacket r.atom).steps + 6) + 2 + 1) *
        NearCubicGates.Close.CellsPack.Gof StageRecovery.packetCallee roleSizes
          (leadOnes (actualRoleRequest r.toRowContext r.atom).word) ^ 2) +
        10 * (actualRoleRequest r.toRowContext r.atom).word.length) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  exact NearCubicGates.Close.CellsPack.lang_le2 _ _ _ _

end NearQuarticWires.StageNativeKids
