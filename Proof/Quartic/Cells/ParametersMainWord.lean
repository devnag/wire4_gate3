import Proof.Quartic.Cells.ParametersCallEncoding
import Proof.Quartic.Cells.ParametersOutputBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open ParameterArithmetic

/-- The nine arithmetic inputs passed from Step 4 to Step 5 have
polynomial bit length, `prop:time`, paper/paper.tex. The bound includes the two actual sampled totals. -/
theorem dispatched_mainWord_envelope {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (Program.mainWord B1 B2 c w).length ≤
      100 * (preparationEnvelope B1 c.n + (callWord c).length + 2) := by
  classical
  let C := Program.runCall c p w
  let V := preparationEnvelope B1 c.n
  let L := (callWord c).length
  let B := 2 * V + L
  have hadm := (Program.dispatch_admitted hd).1
  have hs := prepare_spec _ p.1 p.2
  have hb : 1 ≤ c.radius * (c.n : ℚ) ^ B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hscl := hs.scalar_preparation_bounds B1 hb
  have hnV : c.n ≤ V := (Nat.le_succ _).trans (preparation_envelope_arity B1 c.n)
  have hv : V ≤ 2 ^ V := Nat.lt_two_pow_self.le
  have hVB : V ≤ B := by dsimp [B]; omega
  have hpow : 2 ^ V ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hVB
  have hn (v : ℕ) (h : v ≤ V) : (natWord v).length ≤ 2 * B + 3 :=
    natWord_length_of_power_bound v B (h.trans (hv.trans hpow))
  have h_n := hn c.n hnV
  have h_k := hn p.1.k hscl.k
  have h_MF := hn p.1.MF hscl.MF
  have hQ : p.1.Q ≤ 2 ^ V := by
    rw [hs.Q_eq]
    exact Nat.pow_le_pow_right (by norm_num) hscl.Qexp
  have h_Q := natWord_length_of_power_bound p.1.Q B (hQ.trans hpow)
  have hbounds := selected_output_bounds c p w
  have hnc : C.certifiedColumns.card ≤ 2 ^ V := by
    exact hbounds.2.2.2.1.trans
      (Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le c.n p.1.k).trans hnV))
  have h_nc := natWord_length_of_power_bound C.certifiedColumns.card B (hnc.trans hpow)
  have hM0 : 0 ≤ Program.maskTotal C := hbounds.2.2.2.2.1.trans hbounds.2.2.2.2.2.1
  have hMn : (Program.maskTotal C).natAbs ≤ C.certifiedColumns.card * p.1.Q := by
    apply Int.ofNat_le.mp
    rw [Int.natAbs_of_nonneg hM0, Nat.cast_mul]
    exact hbounds.2.2.2.2.2.2
  have hAn : (Program.acceptTotal C).natAbs ≤ (Program.maskTotal C).natAbs := by
    apply Int.ofNat_le.mp
    rw [Int.natAbs_of_nonneg hbounds.2.2.2.2.1, Int.natAbs_of_nonneg hM0]
    exact hbounds.2.2.2.2.2.1
  have hAB : (Program.maskTotal C).natAbs ≤ 2 ^ B := by
    calc
      (Program.maskTotal C).natAbs ≤ C.certifiedColumns.card * p.1.Q := hMn
      _ ≤ 2 ^ V * 2 ^ V := Nat.mul_le_mul hnc hQ
      _ = 2 ^ (2 * V) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by dsimp [B]; omega)
  have hi (v : ℤ) (h : v.natAbs ≤ 2 ^ B) :
      (NearCubicGates.Close.Interfaces.intWord v).length ≤ 2 * B + 6 := by
    have hm := natWord_length_of_power_bound v.natAbs B h
    have hsign : (natWord (if v < 0 then 1 else 0)).length ≤ 3 := by split_ifs <;> decide
    simp only [NearCubicGates.Close.Interfaces.intWord, List.length_append]
    omega
  have h_A := hi (Program.acceptTotal C) (hAn.trans hAB)
  have h_M := hi (Program.maskTotal C) hAB
  have hc := NearCubicGates.Close.Dispatch.call_bounds c
  have hrat := hs.rational_preparation_bounds B1 L hb hc.2.2.2.1.le hc.2.2.2.2.1.le
  have hratpow : 2 ^ (V + L) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by dsimp [B]; omega)
  have h_eta := ratWord_length_of_power_bounds p.1.eta B
    (hrat.2.1.1.trans hratpow) (hrat.2.1.2.trans hratpow)
  have h_bit : (bitWord (Program.consistentBit C)).length ≤ 3 := by
    cases Program.consistentBit C <;> decide
  simp only [Program.mainWord, Program.stageWord, hd, List.length_cons, List.length_append]
  change ((natWord c.n).length + (natWord p.1.k).length + (natWord p.1.Q).length +
    (natWord p.1.MF).length + (ratWord p.1.eta).length + (natWord C.certifiedColumns.card).length +
    (bitWord (Program.consistentBit C)).length +
    (NearCubicGates.Close.Interfaces.intWord (Program.acceptTotal C)).length +
    (NearCubicGates.Close.Interfaces.intWord (Program.maskTotal C)).length) + 1 ≤ 100 * (V + L + 2)
  dsimp only [B] at *
  omega

/-- The actual word after Step 4 is polynomial in the original call
word on every dispatched call, `prop:time`, paper/paper.tex, uniformly over every witness word. -/
theorem dispatched_mainWord_length {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    (Program.mainWord B1 B2 c w).length ≤
      100 * (preparationCoefficient B1 + 3) * ((callWord c).length + 1) ^ (B1 + 12) := by
  let L := (callWord c).length
  have hn : c.n ≤ L := dispatched_n_le_callWord hd
  have hw := dispatched_mainWord_envelope hd w
  have he : preparationEnvelope B1 c.n ≤ preparationCoefficient B1 * (L + 1) ^ (B1 + 12) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _)
  have hL : L ≤ (L + 1) ^ (B1 + 12) :=
    (Nat.le_succ L).trans (by
      simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (by omega : 1 ≤ B1 + 12))
  have hone : 1 ≤ (L + 1) ^ (B1 + 12) := Nat.pow_pos (Nat.succ_pos _)
  change (Program.mainWord B1 B2 c w).length ≤
    100 * (preparationCoefficient B1 + 3) * (L + 1) ^ (B1 + 12)
  change (Program.mainWord B1 B2 c w).length ≤ 100 * (preparationEnvelope B1 c.n + L + 2) at hw
  nlinarith only [hw, he, hL, hone]

end NearQuarticWires.Cells
