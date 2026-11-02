import Proof.Quartic.StageOutput.EndpointPair
import Proof.Quartic.StageOutput.RationalPrinter

/-!
# Nonnegative center and radius numerators

Paper: `sec:algorithm`, paper/paper.tex. The sum and
difference of the outward-rounded endpoints are formed by natural addition
or subtraction according to the stored sign of the lower endpoint. Both
are divided by the common dyadic denominator `2^(n+1)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def savedRadius : Fin VV := ⟨65, by decide⟩

def centerExpr (negative : Bool) : AE :=
  if negative then .sub (.var savedG) (.var savedF) else .add (.var savedG) (.var savedF)
def radiusExpr (negative : Bool) : AE :=
  if negative then .add (.var savedG) (.var savedF) else .sub (.var savedG) (.var savedF)

def centerAssignments (negative : Bool) : List Assignment :=
  [(normalNum, centerExpr negative), (savedRadius, radiusExpr negative),
   (normalDen, .mul (.lit 2) (.var powerN))]

def centerScratch : List (Fin VV) := [vJ, normalNum, savedRadius, normalDen]

def centerProgram : St VV := .ite (.eq savedSign vZ)
  (assignmentProgram (centerAssignments false)) (assignmentProgram (centerAssignments true))

theorem centerAssignments_legal (negative : Bool) : assignmentsLegal (centerAssignments negative) := by
  cases negative <;>
    simp (config := { decide := true }) [assignmentsLegal, centerAssignments, centerExpr, radiusExpr,
      AE.vars_ok, normalNum, normalDen, savedRadius, savedF, savedG, powerN, vZ, v1, v2, vPOS, VV]

theorem centerAssignments_cost (negative : Bool) : assignmentCost (centerAssignments negative) ≤ 40 := by
  cases negative <;> decide

theorem centerAssignments_safe (negative : Bool) (W : ℕ) (env : Fin VV → ℕ)
    (hcap : env savedF + env savedG + 2 * env powerN + 2 < 2 ^ W) :
    assignmentsSafe W (centerAssignments negative) env := by
  have hsum : env savedG + env savedF < 2 ^ W := by omega
  have hprod : 2 * env powerN < 2 ^ W := by omega
  have htwo : 2 < 2 ^ W := by omega
  cases negative <;>
    simp (config := { decide := true }) [assignmentsSafe, centerAssignments, centerExpr, radiusExpr,
      AE.ok, AE.eval, normalNum, savedRadius] <;> omega

theorem center_value (d : Input) (f g sg : ℕ)
    (hF : (if sg = 0 then (f : ℤ) else -(f : ℤ)) = d.floorValue)
    (hG : (g : ℤ) = d.ceilValue)
    (hcenter : 0 ≤ d.floorValue + d.ceilValue) (hradius : 0 ≤ d.ceilValue - d.floorValue) :
    (if sg = 0 then g + f else g - f) = d.centerNumerator ∧
    (if sg = 0 then g - f else g + f) = d.radiusNumerator := by
  unfold Input.centerNumerator Input.radiusNumerator
  by_cases hsg : sg = 0
  · simp only [hsg, ↓reduceIte] at hF ⊢
    have hc : ((g + f : ℕ) : ℤ) = d.floorValue + d.ceilValue := by omega
    have hr : ((g - f : ℕ) : ℤ) = d.ceilValue - d.floorValue := by omega
    exact ⟨by simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hc, by simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hr⟩
  · simp only [hsg, ↓reduceIte] at hF ⊢
    have hc : ((g - f : ℕ) : ℤ) = d.floorValue + d.ceilValue := by omega
    have hr : ((g + f : ℕ) : ℤ) = d.ceilValue - d.floorValue := by omega
    exact ⟨by simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hc, by simpa only [Int.natAbs_natCast] using congrArg Int.natAbs hr⟩

theorem centerBranch_spec {C : Ctx} (negative : Bool) (a : DS VV) (hc : Cst a)
    (hcap : a.env savedF + a.env savedG + 2 * a.env powerN + 2 < 2 ^ C.Wd) :
    Hs C (assignmentProgram (centerAssignments negative)) a 40 (fun b =>
      b.env normalNum = (if negative then a.env savedG - a.env savedF else a.env savedG + a.env savedF) ∧
      b.env savedRadius = (if negative then a.env savedG + a.env savedF else a.env savedG - a.env savedF) ∧
      b.env normalDen = 2 * a.env powerN ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b centerScratch) := by
  refine Hs.mono (assignmentProgram_spec _ (centerAssignments_legal negative) a hc
    (centerAssignments_safe negative C.Wd a.env hcap)) (centerAssignments_cost negative) ?_
  rintro b ⟨be, bp, bw, bo, bc⟩
  refine ⟨?_, ?_, ?_, bp, bw, bo, bc, (assignmentProgram_frame be).weaken (by cases negative <;> decide)⟩
  · rw [be normalNum (by decide) (by decide)]
    cases negative <;> simp (config := { decide := true })
      [assignmentEnv, centerAssignments, centerExpr, radiusExpr, AE.eval]
  · rw [be savedRadius (by decide) (by decide)]
    cases negative <;> simp (config := { decide := true })
      [assignmentEnv, centerAssignments, centerExpr, radiusExpr, AE.eval]
  · rw [be normalDen (by decide) (by decide)]
    cases negative <;> simp (config := { decide := true })
      [assignmentEnv, centerAssignments, centerExpr, radiusExpr, AE.eval]

theorem centerProgram_spec {C : Ctx} (d : Input) (a : DS VV) (hc : Cst a)
    (hF : (if a.env savedSign = 0 then (a.env savedF : ℤ) else -(a.env savedF : ℤ)) = d.floorValue)
    (hG : (a.env savedG : ℤ) = d.ceilValue) (hn : a.env powerN = 2 ^ d.n)
    (hcenter : 0 ≤ d.floorValue + d.ceilValue) (hradius : 0 ≤ d.ceilValue - d.floorValue)
    (hcap : a.env savedF + a.env savedG + 2 * a.env powerN + 2 < 2 ^ C.Wd) :
    Hs C centerProgram a 41 (fun b =>
      b.env normalNum = d.centerNumerator ∧ b.env savedRadius = d.radiusNumerator ∧
      b.env normalDen = 2 ^ (d.n + 1) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b centerScratch) := by
  have hv := center_value d _ _ _ hF hG hcenter hradius
  refine Hs.ite (c := .eq savedSign vZ) (show savedSign ≠ vZ from by decide) (fun h => ?_) (fun h => ?_)
  · have hs : a.env savedSign = 0 := by simpa [Cnd.eval, hc.z] using h
    refine Hs.mono (centerBranch_spec false a hc hcap) le_rfl ?_
    rintro b ⟨bn, br, bd, bp, bw, bo, bc, bf⟩
    refine ⟨by simpa using bn.trans (by simpa [hs] using hv.1), by simpa using br.trans (by simpa [hs] using hv.2),
      ?_, bp, bw, bo, bc, bf⟩
    simpa [hn, pow_succ, Nat.mul_comm] using bd
  · have hs : a.env savedSign ≠ 0 := by simpa [Cnd.eval, hc.z] using h
    refine Hs.mono (centerBranch_spec true a hc hcap) le_rfl ?_
    rintro b ⟨bn, br, bd, bp, bw, bo, bc, bf⟩
    refine ⟨by simpa using bn.trans (by simpa [hs] using hv.1), by simpa using br.trans (by simpa [hs] using hv.2),
      ?_, bp, bw, bo, bc, bf⟩
    simpa [hn, pow_succ, Nat.mul_comm] using bd

end NearQuarticWires.StageOutput
