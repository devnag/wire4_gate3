import Proof.Quartic.StageMain.Gates
import Proof.Quartic.StageMain.Coefficients
import Proof.Quartic.StageMain.Table
import Proof.Quartic.StageMain.CircuitValue

/-!
# A physical evaluator for the literal circuit word

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Bottom gates, signed top coefficients,
and the Boolean top table are read in their encoded order. The resulting
bit is the exact circuit value at the retained packed sample. Empty lists,
repeated gates, and absent table entries use their literal list semantics.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires
open NearCubicGates.Close.Counter NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def scoreCircuit : St VV := .seq evalGates (.seq evalCoefficients evalTable)
def scoreCircuitScratch : List (Fin VV) := evalGatesScratch ++ evalCoefficientsScratch ++ evalTableScratch

theorem scoreCircuit_spec {C : Ctx} {n : ℕ} (c : NCircuit n)
    (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp = circuitWord c ++ rest)
    (hW : C.cw.length + 4 ≤ C.Wd) (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C scoreCircuit a (800 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env tableResult = (c.eval (packedPoint n (a.env pointSaved))).toNat ∧
      b.cp = a.cp + (circuitWord c).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b scoreCircuitScratch) := by
  have hstart : C.cw.drop a.cp = listWord gateWord c.gates ++
      (listWord intWord c.coeffs ++ (listWord bitWord c.table ++ rest)) := by
    simpa only [circuitWord, List.append_assoc] using hin
  have hlen := len_le_of_drop hin
  have hgatecount : c.gates.length ≤ C.cw.length := by
    have := length_le_flatMap c.gates gateWord (fun g => by
      rw [gateWord_eq, List.length_append, natWord_length]
      omega)
    simp only [circuitWord, listWord, List.length_append] at hlen
    omega
  have hcoefflen : (c.coeffs.flatMap intWord).length ≤ C.cw.length := by
    simp only [circuitWord, listWord, List.length_append] at hlen
    omega
  have habs : c.topWeight < 2 ^ C.cw.length :=
    (sum_natAbs_lt c.coeffs).trans_le (Nat.pow_le_pow_right (by decide) hcoefflen)
  have hwide : 16 * 2 ^ C.cw.length ≤ 2 ^ C.Wd := by
    have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hW
    simpa [pow_add, Nat.mul_comm] using this
  refine Hx.hs (Hs.then (evalGates_spec c.gates _ a hc hstart (by omega) hpoint)
    (fun b ⟨bb, _, bcp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have binput : C.cw.drop b.cp = listWord intWord c.coeffs ++ (listWord bitWord c.table ++ rest) := by
    rw [bcp, drop_adv hstart]
  have bbits : b.env gateBits < 2 ^ C.Wd := by
    rw [bb]
    have hh := bitsValue_lt (gateValues c.gates (a.env pointSaved))
    have hlen : (gateValues c.gates (a.env pointSaved)).length ≤ C.Wd := by
      simp only [gateValues, List.length_map]
      omega
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) hlen)
  refine Hs.then (evalCoefficients_spec c.coeffs _ b bc binput (by omega) bbits)
    (fun d ⟨dp, dn, da, dcp, dw, dout, dc, df⟩ n2 hn2 => ?_)
  have dinput : C.cw.drop d.cp = listWord bitWord c.table ++ rest := by rw [dcp, drop_adv binput]
  have hadd : d.env scorePositive + d.env topAbsolute < 2 ^ C.Wd := by
    rw [dp, da]
    have hh := (score_bounds c.coeffs (b.env gateBits)).1
    change c.topWeight < _ at habs
    change positiveScore c.coeffs (b.env gateBits) ≤ c.topWeight at hh
    change positiveScore c.coeffs (b.env gateBits) + c.topWeight < _
    omega
  refine Hs.last (evalTable_spec c.table rest d dc dinput hW hadd) ?_
  rintro e ⟨er, ep, ew, eo, ec, ef⟩ n3 hn3
  refine ⟨⟨?_, ?_, ew.trans (dw.trans bw), eo.trans (dout.trans bo), ec,
    FrS.trans (bf.weaken (by decide)) (FrS.trans (df.weaken (by decide)) (ef.weaken (by decide)))⟩, ?_⟩
  · rw [er, dp, dn, da, bb]
    change (c.table.getD _ false).toNat = (c.table.getD (c.score _ + c.topWeight).toNat false).toNat
    rw [circuit_index_bits]
    rfl
  · rw [ep, dcp, bcp]
    simp only [circuitWord, List.length_append, Nat.add_assoc]
  · nlinarith only [hn1, hn2, hn3]

end NearQuarticWires.StageMain
