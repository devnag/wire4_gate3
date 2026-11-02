import Proof.Quartic.StageLift.GammaStart
import Proof.Quartic.StageCert.MaskProgram

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells

/-- `sec:cycle` and Step 3, paper/paper.tex: the live outer walk counter is preserved by each mask body. -/
def printWalkIndex : Fin VV := ⟨54, by decide⟩

/-- `sec:cycle` and Step 3, paper/paper.tex: the live outer census is read from the actual Gamma header. -/
def printWalkCount : Fin VV := ⟨55, by decide⟩

/-- `sec:cycle`, paper/paper.tex: the literal
Gamma address uses the original finite-function order, without reversal. -/
def printWalkAt (N : ℕ) (index : Fin (N ^ 8)) : Cycle.Walk N 4 :=
  finFunctionFinEquiv.symm index

/-- `sec:cycle` and `cor:conditional`, paper/paper.tex: a stored coefficient's coordinate has
the actual low-significance-first radix ordering of walkList. -/
theorem printWalkAt_coordinate (N : ℕ) (index : Fin (N ^ 8)) (role : Fin 8) :
    (printWalkAt N index role).val = index.val / N ^ role.val % N := by
  rfl

/-- `cor:conditional`, paper/paper.tex: each
physical Gamma-list position addresses exactly its original closed walk. -/
theorem gammaTable_at {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    (Greedy.gammaTable r.child)[index.val]'(by rw [actualGamma_length]; exact index.isLt) =
      r.child.cellCall.walkWeight r.child.seedPrefix (printWalkAt _ index) := by
  simp only [Greedy.gammaTable, Greedy.walkList, List.getElem_map, List.getElem_ofFn]
  rfl

/-- `lem:print` and Step 3, paper/paper.tex: executable tuple-mask syntax preserves both outer
Gamma loop registers, rather than relying on an informal register choice. -/
theorem mask_preserves_printWalk {a b : DS VV MM}
    (hf : Fr a b (StageCert.Tokens.newtonIndex :: StageCert.Tokens.maskDegreeScratch)) :
    b.env printWalkIndex = a.env printWalkIndex ∧
      b.env printWalkCount = a.env printWalkCount :=
  ⟨hf _ (by decide), hf _ (by decide)⟩

/-- `cor:conditional` and Step 3, paper/paper.tex: start the real all-walk counter by reading the retained
Gamma census and physically setting its ordinal to zero. -/
def startPrintWalks : St VV MM :=
  .seq (startGamma printWalkCount) (.op (.zero printWalkIndex))

/-- `cor:conditional` and Step 3, paper/paper.tex: the initial loop registers are supplied by actual input
operations. Subsequent ordinals are the literal increments of forS. -/
theorem startPrintWalks_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a)
    (hgamma : a.ram gammaStore =
      (NearCubicGates.Close.Interfaces.listWord NearCubicGates.Close.Interfaces.intWord
        (Greedy.gammaTable r.child)).map Bool.toNat)
    (hwidth : natBitLength (r.child.cellCall.seed.N ^ 8) + 2 ≤ C.Wd) :
    Hs C startPrintWalks a
      (a.rc gammaStore + 30 * natBitLength (r.child.cellCall.seed.N ^ 8) + 36)
      (fun b => b.env printWalkIndex = 0 ∧
        b.env printWalkCount = r.child.cellCall.seed.N ^ 8 ∧
        b.rc = Function.update a.rc gammaStore
          (RepairRepresentation.natWord (r.child.cellCall.seed.N ^ 8)).length ∧
        b.ram = a.ram ∧ (b.ip, b.out, b.kin, b.kout, b.kc) =
          (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
        Fr a b (printWalkIndex :: printWalkCount :: rdNatT)) := by
  have hs := startGamma_spec C printWalkCount (by decide) (by decide)
    (Greedy.gammaTable r.child) a hc hgamma (by rw [actualGamma_length]; exact hwidth)
  rw [actualGamma_length] at hs
  unfold startPrintWalks
  refine Hs.seq (t2 := 1) hs fun b ⟨hbn, hbrc, hbram, hbsh, hbc, hbf⟩ => ?_
  refine (hs_zero C printWalkIndex b).mono le_rfl ?_
  rintro d rfl
  have hf : Fr a (b.set printWalkIndex 0) (printWalkIndex :: printWalkCount :: rdNatT) :=
    (hbf.weaken (by
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      tauto)).trans (Fr.set _ _ (by simp))
  refine ⟨rfl, ?_, hbrc, hbram, hbsh, Cst.of_fr hc hf (by decide), hf⟩
  rw [DS.set_env_ne _ _ (by decide)]
  exact hbn

end NearQuarticWires.StageLift
