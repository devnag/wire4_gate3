import Proof.Quartic.StageMain.Coefficient
import Proof.Quartic.StageMain.GateBits

/-!
# Initializing the signed top score

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The encoded coefficient count initializes
the loop, both signed accumulators and the absolute-weight sum start at
zero, and the packed bottom-gate values supply the selected bits.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch
open StageOutput

def coefficientsStartAssignments : List Assignment :=
  [(weightLength, .var t3), (weightIndex, .lit 0), (scorePositive, .lit 0),
   (scoreNegative, .lit 0), (pointWork, .var gateBits), (topAbsolute, .lit 0)]

def coefficientsStart : St VV := .seq readNat (assignmentProgram coefficientsStartAssignments)
def coefficientsStartScratch : List (Fin VV) :=
  [t0, t1, t2, t3, t4, vJ, vPOS, weightLength, weightIndex, scorePositive, scoreNegative, pointWork, topAbsolute]

theorem coefficientsStartAssignments_legal : assignmentsLegal coefficientsStartAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, coefficientsStartAssignments,
    AE.vars_ok, pointWork, scorePositive, scoreNegative, weightIndex, weightLength,
    gateBits, topAbsolute, t3, vZ, v1, v2, vPOS, VV]

theorem coefficientsStart_spec {C : Ctx} (a : DS VV) (hc : Cst a) (n : ℕ) (rest : List Bool)
    (hin : C.cw.drop a.cp = natWord n ++ rest)
    (hW : natBitLength n + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C coefficientsStart a (30 * natBitLength n + 80) (fun b =>
      b.env weightLength = n ∧ b.env weightIndex = 0 ∧
      b.env scorePositive = 0 ∧ b.env scoreNegative = 0 ∧ b.env pointWork = a.env gateBits ∧ b.env topAbsolute = 0 ∧
      b.cp = a.cp + (natWord n).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b coefficientsStartScratch) := by
  refine Hx.hs (Hs.then (readNat_spec a hc n rest hin hW hL)
    (fun b ⟨bn, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bs : assignmentsSafe C.Wd coefficientsStartAssignments b.env := by
    simp [assignmentsSafe, coefficientsStartAssignments, AE.ok]
  refine Hs.last (assignmentProgram_spec coefficientsStartAssignments coefficientsStartAssignments_legal b bc bs) ?_
  rintro e ⟨ee, ep, ew, eo, ec⟩ n2 hn2
  have ev (x : Fin VV) (hx : x.val < 200) (hj : x ≠ vJ) := ee x hx hj
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [ep, bp], by rw [ew, bw], by rw [eo, bo], ec,
    FrS.trans (bf.toS.weaken (by decide)) ((assignmentProgram_frame ee).weaken (by decide))⟩, ?_⟩
  · rw [ev weightLength (by decide) (by decide)]
    simpa (config := { decide := true }) [assignmentEnv, coefficientsStartAssignments, AE.eval] using bn
  · rw [ev weightIndex (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, coefficientsStartAssignments, AE.eval]
  · rw [ev scorePositive (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, coefficientsStartAssignments, AE.eval]
  · rw [ev scoreNegative (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, coefficientsStartAssignments, AE.eval]
  · rw [ev pointWork (by decide) (by decide)]
    simpa (config := { decide := true }) [assignmentEnv, coefficientsStartAssignments, AE.eval] using bf gateBits (by decide)
  · rw [ev topAbsolute (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, coefficientsStartAssignments, AE.eval]
  · have hcost : assignmentCost coefficientsStartAssignments ≤ 49 := by decide
    omega

end NearQuarticWires.StageMain
