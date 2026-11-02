import Proof.Quartic.StageMain.Threshold

/-!
# Reading one top-table entry

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Every table bit is consumed; only the
entry at the requested integer index changes the retained answer.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def tableIndex : Fin VV := ⟨55, by decide⟩
def tableLength : Fin VV := ⟨56, by decide⟩
def tableTarget : Fin VV := ⟨57, by decide⟩
def tableResult : Fin VV := ⟨58, by decide⟩

def tableChoose : St VV :=
  .ite (.eq tableIndex tableTarget) (.op (.copy tableResult t3)) skipS

def tableBit : St VV := .seq readNat tableChoose
def tableBitScratch : List (Fin VV) := readNatT ++ [tableResult]

theorem tableChoose_spec {C : Ctx} (a : DS VV) (hc : Cst a) :
    Hs C tableChoose a 2 (fun b =>
      b.env tableResult = (if a.env tableIndex = a.env tableTarget then a.env t3 else a.env tableResult) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [vJ, tableResult]) := by
  refine Hs.ite (c := .eq tableIndex tableTarget) (show tableIndex ≠ tableTarget by decide)
    (fun h => ?_) (fun h => ?_)
  · have hh : a.env tableIndex = a.env tableTarget := by simpa [Cnd.eval] using h
    refine Hs.mono (hs_copy C tableResult t3 a (by decide)) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [hh], rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
  · have hh : a.env tableIndex ≠ a.env tableTarget := by simpa [Cnd.eval] using h
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by simp (config := { decide := true }) [hh], rfl, rfl, rfl,
      hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩

theorem tableBit_spec {C : Ctx} (a : DS VV) (hc : Cst a) (bit : Bool) (rest : List Bool)
    (hin : C.cw.drop a.cp = bitWord bit ++ rest)
    (hW : 4 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C tableBit a 100 (fun b =>
      b.env tableResult = (if a.env tableIndex = a.env tableTarget then bit.toNat else a.env tableResult) ∧
      b.cp = a.cp + (bitWord bit).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b tableBitScratch) := by
  have he : bitWord bit = natWord bit.toNat := by cases bit <;> rfl
  have hb : natBitLength bit.toNat ≤ 2 := by cases bit <;> decide
  rw [he] at hin
  refine Hx.hs (Hs.then (readNat_spec a hc bit.toNat rest hin (by omega) hL)
    (fun b ⟨bv, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  refine Hs.last (tableChoose_spec b bc) ?_
  rintro e ⟨ev, ep, ew, eo, ec, ef⟩ n2 hn2
  refine ⟨⟨?_, by rw [ep, bp, he], ew.trans bw, eo.trans bo, ec,
    Fr.trans (bf.weaken (by decide)) (ef.weaken (by decide))⟩, by omega⟩
  rw [ev, bv, bf tableIndex (by decide), bf tableTarget (by decide), bf tableResult (by decide)]

end NearQuarticWires.StageMain
