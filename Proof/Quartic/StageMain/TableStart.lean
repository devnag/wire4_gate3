import Proof.Quartic.StageMain.TableBit
import Proof.Quartic.StageMain.Coefficient
import Proof.Gates.Dispatch.ParseCirc

/-!
# Initializing a literal top-table lookup

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The literal list length initializes
the table iterator. Its target is the natural index of the signed score
plus the absolute-weight offset; the answer starts at false.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch
open StageOutput

def tableStartAssignments : List Assignment :=
  [(tableLength, .var t3), (tableIndex, .lit 0), (tableResult, .lit 0), (tableTarget, .sub (.add (.var scorePositive) (.var topAbsolute)) (.var scoreNegative))]
def tableStart : St VV := .seq readNat (assignmentProgram tableStartAssignments)
def tableStartScratch : List (Fin VV) := readNatT ++ [tableLength, tableIndex, tableResult, tableTarget]

theorem tableStartAssignments_legal : assignmentsLegal tableStartAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, tableStartAssignments,
    AE.vars_ok, tableLength, tableIndex, tableResult, tableTarget, scorePositive, topAbsolute, scoreNegative, t3, vZ, v1, v2, vPOS, VV]

theorem tableStart_spec {C : Ctx} (a : DS VV) (hc : Cst a) (G : ℕ) (rest : List Bool)
    (hin : C.cw.drop a.cp = natWord G ++ rest)
    (hW : natBitLength G + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hadd : a.env scorePositive + a.env topAbsolute < 2 ^ C.Wd) :
    Hs C tableStart a (30 * natBitLength G + 100) (fun b =>
      b.env tableLength = G ∧ b.env tableIndex = 0 ∧ b.env tableResult = 0 ∧ b.env tableTarget = (a.env scorePositive + a.env topAbsolute) - a.env scoreNegative ∧
      b.cp = a.cp + (natWord G).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b tableStartScratch) := by
  refine Hx.hs (Hs.then (readNat_spec a hc G rest hin hW hL)
    (fun b ⟨bn, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bpv : b.env scorePositive = a.env scorePositive := bf _ (by decide)
  have bav : b.env topAbsolute = a.env topAbsolute := bf _ (by decide)
  have bnv : b.env scoreNegative = a.env scoreNegative := bf _ (by decide)
  have bs : assignmentsSafe C.Wd tableStartAssignments b.env := by
    simpa (config := { decide := true }) [assignmentsSafe, tableStartAssignments, AE.ok, AE.eval,
      bpv, bav] using hadd
  refine Hs.last (assignmentProgram_spec tableStartAssignments tableStartAssignments_legal b bc bs) ?_
  rintro e ⟨ee, ep, ew, eo, ec⟩ n2 hn2
  have ev (x : Fin VV) (hx : x.val < 200) (hj : x ≠ vJ) := ee x hx hj
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [ep, bp], by rw [ew, bw], by rw [eo, bo], ec,
    FrS.trans (bf.toS.weaken (by decide)) ((assignmentProgram_frame ee).weaken (by decide))⟩, ?_⟩
  · rw [ev tableLength (by decide) (by decide)]
    simpa (config := { decide := true }) [assignmentEnv, tableStartAssignments, AE.eval] using bn
  · rw [ev tableIndex (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, tableStartAssignments, AE.eval]
  · rw [ev tableResult (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, tableStartAssignments, AE.eval]
  · rw [ev tableTarget (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, tableStartAssignments, AE.eval, bpv, bav, bnv]
  · have hcost : assignmentCost tableStartAssignments ≤ 69 := by decide
    omega

end NearQuarticWires.StageMain
