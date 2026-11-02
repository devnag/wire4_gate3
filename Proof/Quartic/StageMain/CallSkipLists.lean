import Proof.Quartic.StageMain.CallSkipScalars

/-!
# Measured lists of scalar circuit fields

`prop:time`, paper/paper.tex: each coefficient,
truth-table bit and parity index is read from its actual list encoding.
The list counters and payload scanners use disjoint registers, and the
retained call-length counter is updated for all fields.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

def scalarIndex : Fin VV := 110
def scalarCount : Fin VV := 111

def scalarListScratch : List (Fin VV) := listScratch scalarIndex scalarCount atomScratch

def skipNatList : St VV MM := skipList scalarIndex scalarCount scanNat

def skipIntList : St VV MM := skipList scalarIndex scalarCount skipInt

theorem skipNatList_spec : ScanSpec skipNatList (listWord natWord) scalarListScratch
    (fun L => 100 * (L + 1) ^ 2) := by
  have h := scanNat_spec.list natWord_positive scalarIndex scalarCount
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h.weaken (fun _ hx => hx) (by intro L; unfold listCost; nlinarith)

theorem skipIntList_spec : ScanSpec skipIntList (listWord intWord) scalarListScratch
    (fun L => 200 * (L + 1) ^ 2) := by
  have h := skipInt_spec.list intWord_positive scalarIndex scalarCount
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h.weaken (fun _ hx => hx) (by intro L; unfold listCost; nlinarith)

theorem skipBitList_spec : ScanSpec skipNatList (listWord bitWord) scalarListScratch
    (fun L => 100 * (L + 1) ^ 2) := by
  have h := skipBit_spec.list bitWord_positive scalarIndex scalarCount
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h.weaken (fun _ hx => hx) (by intro L; unfold listCost; nlinarith)

end NearQuarticWires.StageMain.CallSkip
