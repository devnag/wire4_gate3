import Proof.Quartic.StageOutput.Semantics
import Proof.Quartic.StageOutput.Preservation
import Proof.Quartic.Cells.ParametersOutputCapacityRounding

/-!
# Physical endpoint rounding for Step 5

Paper: `sec:algorithm`, paper/paper.tex. Each endpoint
program first evaluates its literal integer numerator expressions and then
executes signed division with the specified outward rounding direction.
The input fields and binary powers remain unchanged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def endpointScratch : List (Fin VV) := [vJ, roundX, roundY, roundD, roundQ, roundSign]
def lowerEndpoint : St VV := .seq (assignmentProgram lowerAssignments) (roundProgram false)
def upperEndpoint : St VV := .seq (assignmentProgram upperAssignments) (roundProgram true)

theorem lowerEndpoint_spec {C : Ctx} (d : Input) (B : ℕ) (a : DS VV)
    (hc : Cst a) (hs : d.Stored a.env) (hk : a.env powerK = 2 ^ d.k)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hkB : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ C.Wd) (hD : 0 < d.denominator) :
    Hs C lowerEndpoint a 137 (fun b =>
      (if b.env roundSign = 0 then (b.env roundQ : ℤ) else -(b.env roundQ : ℤ)) = d.floorValue ∧
      b.env roundSign ≤ 1 ∧ b.env roundD = d.denominator ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b endpointScratch) := by
  have hcap := Cells.output_lower_assignments_safe d B C.Wd a.env hf hkB hw hs hk
  have hr := Cells.output_lower_rounding_capacity d B C.Wd a.env hf hkB hw hs hk
  refine Hx.hs (Hs.then (lowerNumeratorProgram_spec d a hc hs hk hcap)
    (fun b ⟨bd, bx, byv, be, bp, bw, bo, bc⟩ n1 hn1 => ?_))
  have bf : FrS a b endpointScratch := (assignmentProgram_frame be).weaken (by decide)
  refine Hs.last (roundProgram_spec false b bc (by rw [bd]; exact hD)
    (by rw [bx, byv, bd]; exact hr.1) (by rw [bd]; exact hr.2)) ?_
  rintro e ⟨eq, es, ep, ew, eo, ec, ef⟩ n2 hn2
  refine ⟨⟨by simpa only [bx, byv, bd, Input.floorValue] using eq, es,
    by rw [ef roundD (by decide) (by decide) (by decide) (by decide), bd],
    by rw [ep, bp], by rw [ew, bw], by rw [eo, bo], ec, ?_⟩, ?_⟩
  · apply FrS.trans bf
    intro y hy hnot
    have hh : y ≠ vJ ∧ y ≠ roundX ∧ y ≠ roundY ∧ y ≠ roundD ∧ y ≠ roundQ ∧ y ≠ roundSign := by
      simpa [endpointScratch] using hnot
    exact ef y hy hh.1 hh.2.2.2.2.2 hh.2.2.2.2.1
  · have := lowerAssignments_cost
    omega

theorem upperEndpoint_spec {C : Ctx} (d : Input) (B : ℕ) (a : DS VV)
    (hc : Cst a) (hs : d.Stored a.env) (hn : a.env powerN = 2 ^ d.n)
    (hk : a.env powerK = 2 ^ d.k) (hden : a.env roundD = d.denominator)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hnB : d.n ≤ B) (hkB : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ C.Wd) (hD : 0 < d.denominator) :
    Hs C upperEndpoint a 137 (fun b =>
      (if b.env roundSign = 0 then (b.env roundQ : ℤ) else -(b.env roundQ : ℤ)) = d.ceilValue ∧
      b.env roundSign ≤ 1 ∧ b.env roundD = d.denominator ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b endpointScratch) := by
  have hcap := Cells.output_upper_assignments_safe d B C.Wd a.env hf hnB hkB hw hs hn hk hden
  have hr := Cells.output_upper_rounding_capacity d B C.Wd a.env hf hnB hkB hw hs hn hk hden
  refine Hx.hs (Hs.then (upperNumeratorProgram_spec d a hc hs hn hk hden hcap)
    (fun b ⟨bx, byv, be, bp, bw, bo, bc⟩ n1 hn1 => ?_))
  have bf : FrS a b endpointScratch := (assignmentProgram_frame be).weaken (by decide)
  have bd : b.env roundD = d.denominator := by
    rw [be roundD (by decide) (by decide), assignmentEnv_preserved _ _ _ (by decide), hden]
  refine Hs.last (roundProgram_spec true b bc (by rw [bd]; exact hD)
    (by rw [bx, byv, bd]; exact hr.1) (by rw [bd]; exact hr.2)) ?_
  rintro e ⟨eq, es, ep, ew, eo, ec, ef⟩ n2 hn2
  refine ⟨⟨by simpa only [bx, byv, bd, Input.ceilValue] using eq, es,
    by rw [ef roundD (by decide) (by decide) (by decide) (by decide), bd],
    by rw [ep, bp], by rw [ew, bw], by rw [eo, bo], ec, ?_⟩, ?_⟩
  · apply FrS.trans bf
    intro y hy hnot
    have hh : y ≠ vJ ∧ y ≠ roundX ∧ y ≠ roundY ∧ y ≠ roundD ∧ y ≠ roundQ ∧ y ≠ roundSign := by
      simpa [endpointScratch] using hnot
    exact ef y hy hh.1 hh.2.2.2.2.2 hh.2.2.2.2.1
  · have := upperAssignments_cost
    omega

end NearQuarticWires.StageOutput
