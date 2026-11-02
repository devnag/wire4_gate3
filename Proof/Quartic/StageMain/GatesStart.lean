import Proof.Quartic.StageMain.GateBits
import Proof.Gates.Dispatch.ParseCirc

/-!
# Reading the number of bottom-gate occurrences

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The literal list length initializes
the gate iterator and its packed-result accumulator, while retaining the
sample point and every surrounding field.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch
open StageOutput

def gatesStartAssignments : List Assignment :=
  [(gateCount, .var t3), (gateIndex, .lit 0), (gateBits, .lit 0), (gatePower, .lit 1)]
def gatesStart : St VV := .seq readNat (assignmentProgram gatesStartAssignments)
def gatesStartScratch : List (Fin VV) := readNatT ++ [gateCount, gateIndex, gateBits, gatePower]

theorem gatesStartAssignments_legal : assignmentsLegal gatesStartAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, gatesStartAssignments,
    AE.vars_ok, gateCount, gateIndex, gateBits, gatePower, t3, vZ, v1, v2, vPOS, VV]

theorem gatesStart_spec {C : Ctx} (a : DS VV) (hc : Cst a) (G : ℕ) (rest : List Bool)
    (hin : C.cw.drop a.cp = natWord G ++ rest)
    (hW : natBitLength G + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C gatesStart a (30 * natBitLength G + 70) (fun b =>
      b.env gateCount = G ∧ b.env gateIndex = 0 ∧ b.env gateBits = 0 ∧ b.env gatePower = 1 ∧
      b.cp = a.cp + (natWord G).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b gatesStartScratch) := by
  refine Hx.hs (Hs.then (readNat_spec a hc G rest hin hW hL)
    (fun b ⟨bn, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have htwo : 2 ≤ 2 ^ C.Wd := by
    have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) (show 1 ≤ C.Wd by omega)
    simpa using this
  have bs : assignmentsSafe C.Wd gatesStartAssignments b.env := by
    simp [assignmentsSafe, gatesStartAssignments, AE.ok]
    omega
  refine Hs.last (assignmentProgram_spec gatesStartAssignments gatesStartAssignments_legal b bc bs) ?_
  rintro e ⟨ee, ep, ew, eo, ec⟩ n2 hn2
  have ev (x : Fin VV) (hx : x.val < 200) (hj : x ≠ vJ) := ee x hx hj
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [ep, bp], by rw [ew, bw], by rw [eo, bo], ec,
    FrS.trans (bf.toS.weaken (by decide)) ((assignmentProgram_frame ee).weaken (by decide))⟩, ?_⟩
  · rw [ev gateCount (by decide) (by decide)]
    simpa (config := { decide := true }) [assignmentEnv, gatesStartAssignments, AE.eval] using bn
  · rw [ev gateIndex (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, gatesStartAssignments, AE.eval]
  · rw [ev gateBits (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, gatesStartAssignments, AE.eval]
  · rw [ev gatePower (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, gatesStartAssignments, AE.eval]
  · have hcost : assignmentCost gatesStartAssignments ≤ 39 := by decide
    omega

end NearQuarticWires.StageMain
