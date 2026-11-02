import Proof.Quartic.StageMain.GateStart
import Proof.Quartic.StageMain.GateBounds
import Proof.Quartic.StageMain.Threshold

/-!
# A physical evaluator for an encoded threshold gate

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The program consumes the literal gate
word, evaluates all signed weights at the packed point, and compares the
integer score inclusively with the threshold. Its binary capacity is
bounded by the encoded gate length, including at arity zero.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def scoreGate : St VV := .seq gateStart (.seq scoreWeights finishGate)
def scoreGateScratch : List (Fin VV) :=
  gateStartScratch ++ scoreWeightsScratch ++ finishGateScratch

theorem scoreGate_spec {C : Ctx} {n : ℕ} (g : NormalizedThresholdGate n)
    (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp = gateWord g ++ rest)
    (hW : C.cw.length + 3 ≤ C.Wd) (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C scoreGate a (200 * (C.cw.length + 2) ^ 2) (fun b =>
      b.env gateResult = (g.eval (packedPoint n (a.env pointSaved))).toNat ∧
      b.cp = a.cp + (gateWord g).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b scoreGateScratch) := by
  let ws := List.ofFn g.weight
  have hlen := len_le_of_drop hin
  have hb := gate_encoding_bounds g
  have hcap := gate_score_capacity g hlen hW
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have hh := Nat.lt_two_pow_self (n := C.Wd)
    omega
  have hstart : C.cw.drop a.cp = natWord n ++ (ws.flatMap NearCubicGates.Close.Interfaces.intWord ++ NearCubicGates.Close.Interfaces.intWord g.threshold ++ rest) := by
    simpa only [gateWord_eq, List.append_assoc] using hin
  refine Hx.hs (Hs.then (gateStart_spec a hc n _ hstart (by omega) hL)
    (fun b ⟨bl, bi, bp, bn, bx, bcp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have binput : C.cw.drop b.cp = ws.flatMap NearCubicGates.Close.Interfaces.intWord ++ (NearCubicGates.Close.Interfaces.intWord g.threshold ++ rest) := by
    rw [bcp, drop_adv hstart, List.append_assoc]
  have blen : b.env weightLength = ws.length := by simpa [ws] using bl
  have bcap : b.env scorePositive + b.env scoreNegative + 3 * (ws.map Int.natAbs).sum + 1 < 2 ^ C.Wd := by
    rw [bp, bn]
    dsimp [ws]
    omega
  refine Hs.then (scoreWeights_spec ws _ b bc bi blen binput (by omega) hL
    (by simp only [ws, List.length_ofFn]; omega) (by rw [bx]; exact hpoint) bcap)
    (fun d ⟨dp, dn, dx, dcp, dw, dout, dc, df, _, _⟩ n2 hn2 => ?_)
  have dinput : C.cw.drop d.cp = NearCubicGates.Close.Interfaces.intWord g.threshold ++ rest := by rw [dcp, drop_adv binput]
  have dbounds := score_bounds ws (a.env pointSaved)
  have dcap : d.env scorePositive + d.env scoreNegative + g.threshold.natAbs < 2 ^ C.Wd := by
    rw [dp, dn, bp, bn, bx]
    dsimp [ws] at dbounds ⊢
    omega
  refine Hs.last (finishGate_spec d dc g.threshold rest dinput (by omega) hL dcap) ?_
  rintro e ⟨eg, ep, ew, eo, ec, ef⟩ n3 hn3
  refine ⟨⟨?_, ?_, by rw [ew, dw, bw], by rw [eo, dout, bo], ec,
    FrS.trans (bf.weaken (by decide))
      (FrS.trans (df.weaken (by decide))
        (ef.toS.weaken (by decide)))⟩, ?_⟩
  · rw [eg, dp, dn, bp, bn, bx, gate_eval_packed]
    simp only [Nat.zero_add, ws]
  · rw [ep, dcp, bcp, gateWord_eq, List.length_append, List.length_append]
    simp only [ws, Nat.add_assoc]
  · have hn : ws.length ≤ C.cw.length := by simpa [ws] using hb.1.trans hlen
    have ht : (NearCubicGates.Close.Interfaces.intWord g.threshold).length ≤ C.cw.length := by
      rw [gateWord_eq, List.length_append, List.length_append] at hlen
      omega
    have hnb : natBitLength n ≤ C.cw.length := hb.2.1.trans hlen
    nlinarith only [hn1, hn2, hn3, hnb, ht, Nat.mul_le_mul_right (60 * C.cw.length + 129) hn]

end NearQuarticWires.StageMain
