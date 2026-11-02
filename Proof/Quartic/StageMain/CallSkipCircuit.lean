import Proof.Quartic.StageMain.CallSkipLists

/-!
# Measured traversal of both threshold-circuit levels

`def:class`, paper/paper.tex, and `prop:time`: each bottom gate contributes its weight list and
threshold; the top level contributes its coefficient and Boolean
acceptance lists. Repeated and empty lists are read in literal order.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

def skipGate : St VV MM := .seq skipIntList skipInt

theorem skipGate_spec {n : ℕ} : ScanSpec skipGate (@gateWord n) scalarListScratch
    (fun L => 400 * (L + 1) ^ 2) := by
  have h := (skipIntList_spec.map (fun g : NormalizedThresholdGate n => List.ofFn g.weight)).seq
    (skipInt_spec.map NormalizedThresholdGate.threshold)
  refine h.weaken ?_ (by
    intro L
    have hpow : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hpos : 0 < (L + 1) ^ 3 := by positivity
    nlinarith only [hpow, hpos])
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hx
  · exact List.mem_append_left _ hx

theorem gateWord_positive {n : ℕ} (g : NormalizedThresholdGate n) : 0 < (gateWord g).length := by
  have h := intWord_positive g.threshold
  simp only [gateWord, List.length_append]
  omega

def gateIndex : Fin VV := 112
def gateCount : Fin VV := 113

def gateListScratch : List (Fin VV) := listScratch gateIndex gateCount scalarListScratch

def skipGateList : St VV MM := skipList gateIndex gateCount skipGate

theorem skipGateList_spec {n : ℕ} : ScanSpec skipGateList (listWord (@gateWord n)) gateListScratch
    (fun L => 500 * (L + 1) ^ 3) := by
  have h := (@skipGate_spec n).list gateWord_positive gateIndex gateCount
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h.weaken (fun _ hx => hx) (by intro L; unfold listCost; nlinarith)

def skipCircuit : St VV MM := .seq skipGateList (.seq skipIntList skipNatList)

theorem scalarScratch_in_gate : ∀ x ∈ scalarListScratch, x ∈ gateListScratch := by
  intro x hx
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

theorem skipCircuit_spec {n : ℕ} : ScanSpec skipCircuit (@circuitWord n) gateListScratch
    (fun L => 1000 * (L + 1) ^ 3) := by
  have h := ((@skipGateList_spec n).map NCircuit.gates).seq
    ((skipIntList_spec.map NCircuit.coeffs).seq (skipBitList_spec.map NCircuit.table))
  have heq : (fun C : NCircuit n => listWord gateWord C.gates ++
      (listWord intWord C.coeffs ++ listWord bitWord C.table)) = circuitWord := by
    funext C
    simp only [circuitWord, List.append_assoc]
  rw [heq] at h
  refine h.weaken ?_ (by
    intro L
    have hpow : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hpos : 0 < (L + 1) ^ 3 := by positivity
    nlinarith only [hpow, hpos])
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hx
  · rcases List.mem_append.mp hx with hx | hx <;> exact scalarScratch_in_gate x hx

end NearQuarticWires.StageMain.CallSkip
