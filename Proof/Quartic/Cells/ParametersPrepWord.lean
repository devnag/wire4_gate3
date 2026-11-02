import Proof.Quartic.Cells.ParametersCallEncoding
import Proof.Quartic.Cells.ParametersDefaultWord
import Proof.Quartic.Cells.ParametersMainWord

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open ParameterArithmetic

/-- The witness prefix actually read has polynomial length,
`sec:params` and `prop:time`, paper/paper.tex. Its length is independent of any unused witness suffix. -/
theorem selected_witnessReadLength_bound (c : Call) (p : Program.Selected c) :
    Program.witnessReadLength c p.1 ≤ 5 * (c.n + 1) ^ 5 := by
  have hs := prepare_spec _ p.1 p.2
  have hc : CoreRules (Builder.callInput c) p.1 := hs
  have hmu : p.1.mu ≤ c.n := hc.mu_le_lambda.trans hc.lambda_le_n
  have hJ : p.1.J + 1 ≤ 2 * (c.n + 1) := by
    have hj := hs.J_bound
    rw [hs.Jmax_eq] at hj
    omega
  have hG : c.first.gates.length + c.second.gates.length ≤ 2 * c.n ^ 4 :=
    hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
  have hn : c.n ≤ (c.n + 1) ^ 5 := (Nat.le_succ c.n).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos c.n) (by norm_num : 1 ≤ 5))
  change p.1.k + (p.1.J + 1) * (c.first.gates.length + c.second.gates.length) ≤ _
  calc
    p.1.k + (p.1.J + 1) * (c.first.gates.length + c.second.gates.length) ≤
        c.n + (2 * (c.n + 1)) * (2 * (c.n + 1) ^ 4) :=
      Nat.add_le_add hs.k_lt_n.le (Nat.mul_le_mul hJ
        (hG.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_succ _) _))))
    _ = c.n + 4 * (c.n + 1) ^ 5 := by ring
    _ ≤ 5 * (c.n + 1) ^ 5 := by omega

/-- The complete dispatched preparation word, including the
zero-filled witness prefix, is polynomial in the actual call word,
`prop:time`, paper/paper.tex. -/
theorem dispatched_prepWord_length {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (Program.prepWord B1 B2 c w).length ≤
      200 * (preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12) := by
  let L := (callWord c).length
  have hn : c.n ≤ L := dispatched_n_le_callWord hd
  have hp := dispatched_parametersWord_length hd
  have hread : Program.witnessReadLength c p.1 ≤ 5 * (L + 1) ^ (B1 + 12) :=
    (selected_witnessReadLength_bound c p).trans
      (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _).trans
        (Nat.pow_le_pow_right (Nat.succ_pos L) (by omega))))
  have hL : L ≤ (L + 1) ^ (B1 + 12) := (Nat.le_succ L).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (by omega : 1 ≤ B1 + 12))
  have hone : 1 ≤ (L + 1) ^ (B1 + 12) := Nat.pow_pos (Nat.succ_pos _)
  simp only [Program.prepWord, Program.stageWord, hd, List.length_cons, List.length_append,
    NearCubicGates.Close.Dispatch.frame_length, Program.witnessPrefix, List.length_ofFn]
  change L + (Program.parametersWord p.1).length + (2 * Program.witnessReadLength c p.1 + 1) + 1 ≤
    200 * (preparationCoefficient B1 + 5) * (L + 1) ^ (B1 + 12)
  change (Program.parametersWord p.1).length ≤
    100 * (preparationCoefficient B1 + 4) * (L + 1) ^ (B1 + 12) at hp
  nlinarith only [hp, hread, hL, hone, Nat.zero_le (preparationCoefficient B1 * (L + 1) ^ (B1 + 12))]

/-- The preparation word is polynomial in the call word on every
call and every witness, including all default branches,
`prop:time`, paper/paper.tex. -/
theorem all_calls_prepWord_length (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (Program.prepWord B1 B2 c w).length ≤
      200 * (preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12) := by
  classical
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    have ho := nondispatched_outputWord_length c w hd
    have hone : 1 ≤ ((callWord c).length + 1) ^ (B1 + 12) := Nat.pow_pos (Nat.succ_pos _)
    have hb : 25 ≤ 200 * (preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12) := by
      have hh := Nat.mul_le_mul (show 25 ≤ 200 * (preparationCoefficient B1 + 5) by omega) hone
      simpa only [Nat.mul_one] using hh
    simpa only [Program.prepWord, Program.stageWord, hd, List.length_cons] using
      (Nat.add_le_add_right ho 1).trans hb
  | some p => exact dispatched_prepWord_length hd w

/-- The Step 4 arithmetic word also has a uniform polynomial bound
on all calls, `prop:time`, paper/paper.tex. -/
theorem all_calls_mainWord_length (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (Program.mainWord B1 B2 c w).length ≤
      200 * (preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12) := by
  classical
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    have ho := nondispatched_mainWord_length c w hd
    have hone : 1 ≤ ((callWord c).length + 1) ^ (B1 + 12) := Nat.pow_pos (Nat.succ_pos _)
    have hh := Nat.mul_le_mul (show 25 ≤ 200 * (preparationCoefficient B1 + 5) by omega) hone
    exact ho.trans (by simpa only [Nat.mul_one] using hh)
  | some p =>
    exact (dispatched_mainWord_length hd w).trans
      (Nat.mul_le_mul_right _ (by omega :
        100 * (preparationCoefficient B1 + 3) ≤ 200 * (preparationCoefficient B1 + 5)))

end NearQuarticWires.Cells
