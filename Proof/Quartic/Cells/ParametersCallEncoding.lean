import Proof.Quartic.Cells.ParametersRecordWords
import Proof.Quartic.Program.Output
import Proof.Gates.Dispatch.Main

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open ParameterArithmetic

/-- Unit top coefficients count actual occurrences, `def:class` and
the call normalization, paper/paper.tex. -/
theorem unit_topWeight_eq_occurrences {n B : ℕ} (C : NCircuit n)
    (hw : C.WellFormed B) (hu : Transfer.UnitTop C) : C.topWeight = C.gates.length := by
  have hm : C.coeffs.map Int.natAbs = List.replicate C.coeffs.length 1 :=
    List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
      rw [hu a ha]
      rfl⟩
  unfold NCircuit.topWeight
  rw [hm, List.sum_replicate, smul_eq_mul, mul_one, ← hw.1]

/-- A nonzero-wire normalized call has nonzero total top weight,
`sec:counting`, paper/paper.tex. This permits the literal call-word
arity bound without imposing a size condition on zero-wire calls. -/
theorem admitted4_nonzero_topWeight {B1 B2 : ℕ} {c : Call}
    (hadm : Transfer.Admitted4 B1 B2 c) (hW : Transfer.callWires c ≠ 0) : c.W ≠ 0 := by
  obtain ⟨_, hf, hs, hu1, hu2, _⟩ := hadm
  intro hzero
  have h1 := unit_topWeight_eq_occurrences c.first hf hu1
  have h2 := unit_topWeight_eq_occurrences c.second hs hu2
  have hfzero : c.first.gates.length = 0 := by unfold Call.W at hzero; omega
  have hszero : c.second.gates.length = 0 := by unfold Call.W at hzero; omega
  have hfempty := List.length_eq_zero_iff.mp hfzero
  have hsempty := List.length_eq_zero_iff.mp hszero
  exact hW (by simp [Transfer.callWires, Transfer.wires, hfempty, hsempty])

/-- A dispatched call pays for its input arity in its actual call
word, `prop:time`, paper/paper.tex. -/
theorem dispatched_n_le_callWord {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) : c.n ≤ (callWord c).length := by
  obtain ⟨hadm, hW⟩ := Program.dispatch_admitted hd
  exact NearCubicGates.Close.Dispatch.n_le_callWord B1 B2 c
    (Program.admitted_of_admitted4 hadm) (admitted4_nonzero_topWeight hadm hW)

/-- The literal selected parameter word is polynomially bounded in
the serialized input call, including both rational precision fields
and both lists, `prop:time`, paper/paper.tex. -/
theorem dispatched_parametersWord_length {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    (Program.parametersWord p.1).length ≤
      100 * (preparationCoefficient B1 + 4) * ((callWord c).length + 1) ^ (B1 + 12) := by
  let L := (callWord c).length
  have hn : c.n ≤ L := dispatched_n_le_callWord hd
  have hadm := (Program.dispatch_admitted hd).1
  have hs := prepare_spec _ p.1 p.2
  have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hc := NearCubicGates.Close.Dispatch.call_bounds c
  have hword := hs.parametersWord_preparation_bound B1 L hb hc.2.2.2.1.le hc.2.2.2.2.1.le
  have henv : preparationEnvelope B1 c.n ≤ preparationCoefficient B1 * (L + 1) ^ (B1 + 12) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _)
  have hL : L ≤ (L + 1) ^ (B1 + 12) := by
    calc
      L ≤ L + 1 := Nat.le_succ _
      _ = (L + 1) ^ 1 := by rw [pow_one]
      _ ≤ (L + 1) ^ (B1 + 12) := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have hn2 : (c.n + 1) ^ 2 ≤ (L + 1) ^ (B1 + 12) :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
  have hone : 1 ≤ (L + 1) ^ (B1 + 12) := Nat.pow_pos (Nat.succ_pos _)
  change (Program.parametersWord p.1).length ≤ _ at hword
  change (Program.parametersWord p.1).length ≤ 100 * (preparationCoefficient B1 + 4) * (L + 1) ^ (B1 + 12)
  change (Program.parametersWord p.1).length ≤
    100 * (preparationEnvelope B1 c.n + L + (c.n + 1) ^ 2 + 2) at hword
  nlinarith only [hword, henv, hL, hn2, hone]

end NearQuarticWires.Cells
