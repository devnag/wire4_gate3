import Proof.Quartic.StageMain.CallSizeWords
import Proof.Quartic.StageMain.HeaderWidth

/-!
# Polynomial size of every admitted original call

The normalized calls of `thm:counter`, paper/paper.tex,
have at most `2 n^4` wires, bounded dense integer rows, explicit unit
coefficients and truth tables, and a radius word of length at most
`n^B₂`. Thus the workspace of `prop:time`, can be
allocated from the arity header alone, independently of later tables.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSize

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces

theorem B0_le (n : ℕ) : Call.B0 n ≤ 4 * (n + 1) ^ 2 := by
  have h := NearCubicGates.Close.Counter.clog_le_self (n + 1)
  unfold Call.B0
  nlinarith

theorem circuitWord_polynomial {n : ℕ} (C : NCircuit n)
    (hn : 4 ≤ n) (hw : C.WellFormed (Call.B0 n)) (hu : Transfer.UnitTop C) :
    (circuitWord C).length ≤ 40 * (C.gates.length + 1) * (n + 1) ^ 3 := by
  have hB : 1 ≤ Call.B0 n := by
    have hlog : 1 ≤ Nat.clog 2 (n + 1) := Nat.clog_pos (by decide) (by omega)
    unfold Call.B0
    nlinarith
  have h := circuitWord_le C hw hu hB
  have hb := B0_le n
  have hK : 2 * n + 3 + (n + 1) * (2 * Call.B0 n + 4) + 20 ≤
      40 * (n + 1) ^ 3 := by nlinarith
  have hh := Nat.mul_le_mul_left C.gates.length hK
  have hpos : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [h, hh, hpos]

theorem admitted_callWord_length {B1 B2 : ℕ} {c : Call}
    (hadm : Transfer.Admitted4 B1 B2 c) :
    (callWord c).length ≤ 1000 * (c.n + 1) ^ 8 + (c.n + 1) ^ B2 := by
  obtain ⟨hn, hf, hs, hu1, hu2, _hkind, _hparity, hpar, hwires, _hrlo, _hrhi, hr, hplen⟩ := hadm
  have hfirst := circuitWord_polynomial c.first hn hf hu1
  have hsecond := circuitWord_polynomial c.second hn hs hu2
  have hg1 := gates_le_wires c.first
  have hg2 := gates_le_wires c.second
  have hg : c.first.gates.length + c.second.gates.length ≤ 2 * c.n ^ 4 := by
    unfold Transfer.callWires at hwires
    omega
  have hnpow : c.n ^ 4 ≤ (c.n + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hpositive : 1 ≤ (c.n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hg' : c.first.gates.length + c.second.gates.length + 2 ≤ 4 * (c.n + 1) ^ 4 := by
    omega
  have hmul := Nat.mul_le_mul_right (40 * (c.n + 1) ^ 3) hg'
  have hcircuit : (circuitWord c.first).length + (circuitWord c.second).length ≤
      160 * (c.n + 1) ^ 7 := by
    calc
      _ ≤ 40 * (c.first.gates.length + c.second.gates.length + 2) * (c.n + 1) ^ 3 := by
        nlinarith only [hfirst, hsecond]
      _ ≤ 160 * (c.n + 1) ^ 7 := by nlinarith only [hmul]
  have hparword := listWord_le natWord c.parity (2 * c.n + 3) (by
    intro v hv
    have hp := hpar v hv
    exact (natWord_le v).trans (by omega))
  have hparmul := Nat.mul_le_mul_right (2 * c.n + 3) hplen
  have hparity : (listWord natWord c.parity).length ≤ 10 * (c.n + 1) ^ 2 := by
    nlinarith only [hparword, hparmul, hplen]
  have hnat := natWord_le c.n
  have hkind : (natWord (kindTag c.kind)).length ≤ 7 := by cases c.kind <;> decide
  have hpow2 : (c.n + 1) ^ 2 ≤ (c.n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hpow7 : (c.n + 1) ^ 7 ≤ (c.n + 1) ^ 8 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hpow1 : c.n + 1 ≤ (c.n + 1) ^ 8 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ c.n + 1) (by decide : 1 ≤ 8)
  have hpow0 : 1 ≤ (c.n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hrpow : c.n ^ B2 ≤ (c.n + 1) ^ B2 := Nat.pow_le_pow_left (by omega) B2
  simp only [callWord, List.length_append]
  omega

theorem admitted_callWord_polynomial {B1 B2 : ℕ} {c : Call}
    (hadm : Transfer.Admitted4 B1 B2 c) :
    (callWord c).length ≤ 1001 * (c.n + 1) ^ (B2 + 8) := by
  have h := admitted_callWord_length hadm
  have h1 : (c.n + 1) ^ 8 ≤ (c.n + 1) ^ (B2 + 8) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (c.n + 1) ^ B2 ≤ (c.n + 1) ^ (B2 + 8) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem dispatched_callWord_polynomial {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    (callWord c).length ≤ 1001 * (c.n + 1) ^ (B2 + 8) :=
  admitted_callWord_polynomial (Program.dispatch_admitted hd).1

end NearQuarticWires.StageMain.CallSize
