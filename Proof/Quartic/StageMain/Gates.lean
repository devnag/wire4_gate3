import Proof.Quartic.StageMain.GatesStart
import Proof.Quartic.StageMain.GatesLoop

/-!
# The literal bottom-gate-list evaluator

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Reading the list header and all gate
records produces the packed list of exact bottom-gate values. The work
is polynomial in the serialized circuit prefix, including the empty list.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Counter NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def evalGates : St VV := .seq gatesStart gatesLoop
def evalGatesScratch : List (Fin VV) := gatesStartScratch ++ gatesLoopScratch

theorem evalGates_spec {C : Ctx} {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hin : C.cw.drop a.cp = listWord gateWord gs ++ rest)
    (hW : C.cw.length + 3 ≤ C.Wd) (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C evalGates a (300 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env gateBits = bitsValue (gateValues gs (a.env pointSaved)) ∧ b.env gateCount = gs.length ∧
      b.cp = a.cp + (listWord gateWord gs).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b evalGatesScratch) := by
  have hinput : C.cw.drop a.cp = natWord gs.length ++ (gs.flatMap gateWord ++ rest) := by
    simpa only [listWord, List.append_assoc] using hin
  have hl := len_le_of_drop hin
  have hcount : gs.length ≤ C.cw.length := by
    have hh := length_le_flatMap gs gateWord (fun g => by
      rw [gateWord_eq, List.length_append, natWord_length]
      omega)
    simp only [listWord, List.length_append] at hl
    omega
  have hb : natBitLength gs.length ≤ C.cw.length := by
    have := natBitLength_le_len gs.length
    simp only [listWord, List.length_append] at hl
    omega
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (gatesStart_spec a hc gs.length _ hinput (by omega) hL)
    (fun b ⟨bn, bi, bb, bp, bcp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bx : b.env pointSaved = a.env pointSaved := bf _ (by decide) (by decide)
  have binput : C.cw.drop b.cp = gs.flatMap gateWord ++ rest := by rw [bcp, drop_adv hinput]
  refine Hs.last (gatesLoop_spec gs rest b bc bi bn bb bp binput hW hcount (by rw [bx]; exact hpoint)) ?_
  rintro e ⟨eb, _, ep, ew, eo, ec, ef, _, en⟩ n2 hn2
  refine ⟨⟨by rw [eb, bx], en, ?_, ew.trans bw, eo.trans bo, ec,
    FrS.trans (bf.weaken (by decide)) (ef.weaken (by decide))⟩, ?_⟩
  · rw [ep, bcp]
    simp only [listWord, List.length_append, Nat.add_assoc]
  · have hh := Nat.mul_le_mul_right (200 * (C.cw.length + 2) ^ 2 + 45) hcount
    nlinarith only [hn1, hn2, hb, hh]

end NearQuarticWires.StageMain
