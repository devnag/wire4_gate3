import Proof.Quartic.StagePrep.CensusCircuit
import Proof.Gates.Dispatch.ParseCall

/-!
# The public call's physical wire and unit-top census

Paper: `def:class`, paper/paper.tex, normalized
calls, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation (natWord)

/-- The call census of `sec:counting`, paper/paper.tex reads the
public header and each of the two encoded circuit lists. -/
def censusCall : St VV := .seq pHead (.seq censusCircuit censusCircuit)

/-- The circuit wire count is paid by the original call encoding
in `sec:counting`, paper/paper.tex. -/
theorem wires_le_circuitWord {n : ℕ} (Cc : NCircuit n) :
    Transfer.wires Cc ≤ (circuitWord Cc).length := by
  have hg := gateChargeSum_le_wordlength Cc.gates
  change gateChargeSum Cc.gates ≤ _
  simp only [circuitWord, listWord, List.length_append]
  omega

/-- The call census in `sec:counting`, paper/paper.tex computes
both actual wire counts and all unit coefficients in a cubic
number of language steps, independently of the witness. -/
theorem censusCall_spec (C : Ctx) (c : Call) (a : DS VV) (hc : Cst a)
    (hcp : a.cp = 0) (ht : a.env censusTotal = 0) (hf : a.env censusUnit = 1)
    (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : 2 * C.cw.length + 4 < 2 ^ C.Wd) :
    Hs C censusCall a (1200 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env censusTotal = Transfer.callWires c ∧
      b.env censusUnit = bnat (Transfer.UnitTop c.first ∧ Transfer.UnitTop c.second) ∧
      b.cp = pos3 c ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b (headT ++ circuitCensusT)) := by
  have hword := congrArg List.length (callWord_eq c)
  simp only [List.length_append] at hword
  have hfirst : (circuitWord c.first).length ≤ C.cw.length := by rw [hcw]; omega
  have hboth : (circuitWord c.first).length + (circuitWord c.second).length ≤ C.cw.length := by
    rw [hcw]
    omega
  have hstart : C.cw.drop a.cp = natWord c.n ++ natWord (kindTag c.kind) ++
      (circuitWord c.first ++ (circuitWord c.second ++
        (listWord natWord c.parity ++ ratWord c.radius))) := by
    rw [hcp, List.drop_zero, hcw, callWord_eq]
  unfold censusCall
  refine Hx.hs (Hs.then (pHead_spec c a hc _ hstart hW (by omega))
    (fun b ⟨_, _, _, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbpos : b.cp = pos1 c := by simp only [hbcp, hcp, Nat.zero_add, pos1]
  have hbcw : C.cw.drop b.cp = circuitWord c.first ++
      (circuitWord c.second ++ (listWord natWord c.parity ++ ratWord c.radius)) := by
    rw [hbcp]
    have hd := drop_adv (by simpa only [List.append_assoc] using hstart :
      C.cw.drop a.cp = (natWord c.n ++ natWord (kindTag c.kind)) ++ _)
    simpa only [List.length_append, Nat.add_assoc] using hd
  have hbt : b.env censusTotal = 0 := (hbfr _ (by decide)).trans ht
  have hbf : b.env censusUnit = bnat True := by rw [hbfr _ (by decide), hf]; rfl
  refine Hs.then (censusCircuit_spec C c.first _ b hbc True hbf hbcw
    (by omega) (by omega) (by rw [hbt]; omega))
    (fun d ⟨hdt, hdf, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdcw : C.cw.drop d.cp = circuitWord c.second ++
      (listWord natWord c.parity ++ ratWord c.radius) := by
    rw [hdcp, ← List.drop_drop, hbcw, List.drop_left]
  have hdt' : d.env censusTotal = Transfer.wires c.first := by simpa only [hbt, Nat.zero_add] using hdt
  have hdf' : d.env censusUnit = bnat (Transfer.UnitTop c.first) := by simpa only [true_and] using hdf
  have hwt := wires_le_circuitWord c.first
  refine Hs.last (censusCircuit_spec C c.second _ d hdc (Transfer.UnitTop c.first)
    hdf' hdcw (by omega) (by omega) (by rw [hdt']; omega))
    (fun e ⟨het, hef, hecp, hewq, heout, hec, hefr⟩ n3 hn3 => ?_)
  refine ⟨⟨?_, hef, ?_, hewq.trans (hdwq.trans hbwq),
    heout.trans (hdout.trans hbout), hec,
    Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.weaken hdfr (by decide)) (Fr.weaken hefr (by decide)))⟩, ?_⟩
  · rw [het, hdt']
    rfl
  · rw [hecp, hdcp, hbpos]
    rfl
  · have hpow : C.cw.length + 2 ≤ (C.cw.length + 2) ^ 3 :=
      Nat.le_self_pow (by norm_num) _
    omega

end NearQuarticWires.StagePrep
