import Proof.Quartic.StageMain.ParityBit
import Proof.Gates.Dispatch.ParseCirc

/-!
# Reading the number of parity indices

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The literal list length initializes
the parity iterator and its Boolean accumulator, while retaining the
sample point, call arity and every surrounding field.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch
open StageOutput

def parityStartAssignments : List Assignment :=
  [(parityLength, .var t3), (parityIndex, .lit 0), (parityResult, .lit 0)]
def parityStart : St VV := .seq readNat (assignmentProgram parityStartAssignments)
def parityStartScratch : List (Fin VV) := readNatT ++ [parityLength, parityIndex, parityResult]

theorem parityStartAssignments_legal : assignmentsLegal parityStartAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, parityStartAssignments,
    AE.vars_ok, parityLength, parityIndex, parityResult, t3, vZ, v1, v2, vPOS, VV]

theorem parityStart_spec {C : Ctx} (a : DS VV) (hc : Cst a) (G : ℕ) (rest : List Bool)
    (hin : C.cw.drop a.cp = natWord G ++ rest)
    (hW : natBitLength G + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C parityStart a (30 * natBitLength G + 70) (fun b =>
      b.env parityLength = G ∧ b.env parityIndex = 0 ∧ b.env parityResult = 0 ∧
      b.cp = a.cp + (natWord G).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b parityStartScratch) := by
  refine Hx.hs (Hs.then (readNat_spec a hc G rest hin hW hL)
    (fun b ⟨bn, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bs : assignmentsSafe C.Wd parityStartAssignments b.env := by
    simp [assignmentsSafe, parityStartAssignments, AE.ok]
  refine Hs.last (assignmentProgram_spec parityStartAssignments parityStartAssignments_legal b bc bs) ?_
  rintro e ⟨ee, ep, ew, eo, ec⟩ n2 hn2
  have ev (x : Fin VV) (hx : x.val < 200) (hj : x ≠ vJ) := ee x hx hj
  refine ⟨⟨?_, ?_, ?_, by rw [ep, bp], by rw [ew, bw], by rw [eo, bo], ec,
    FrS.trans (bf.toS.weaken (by decide)) ((assignmentProgram_frame ee).weaken (by decide))⟩, ?_⟩
  · rw [ev parityLength (by decide) (by decide)]
    simpa (config := { decide := true }) [assignmentEnv, parityStartAssignments, AE.eval] using bn
  · rw [ev parityIndex (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, parityStartAssignments, AE.eval]
  · rw [ev parityResult (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, parityStartAssignments, AE.eval]
  · have hcost : assignmentCost parityStartAssignments ≤ 39 := by decide
    omega

end NearQuarticWires.StageMain
