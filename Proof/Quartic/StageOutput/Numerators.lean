import Proof.Quartic.StageOutput.Assignments
import Proof.Quartic.StageOutput.Layout
import Proof.Quartic.StageOutput.Rounding

/-!
# Integer numerator expressions for Step 5

Paper: `sec:algorithm`, paper/paper.tex. The endpoint
formulas use the common denominator `Q * eta.den` and exact natural
positive and negative parts. Registers 50 and 51 hold `2^n` and `2^k`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def powerN : Fin VV := ⟨50, by decide⟩
def powerK : Fin VV := ⟨51, by decide⟩

def denominatorExpr : AE := .mul (.var 22) (.var 26)
def lowerPositiveExpr : AE := .mul (.mul (.var powerK) (.var 30)) (.var 26)
def lowerNegativeExpr : AE :=
  .mul (.mul (.mul (.mul (.mul (.var powerK) (.lit 2)) (.var 23)) (.var 27)) (.var 25)) (.var 22)
def upperPositiveExpr : AE :=
  .add (.mul (.var powerK)
    (.add (.mul (.var 30) (.var 26))
      (.mul (.mul (.mul (.add (.mul (.lit 2) (.var 23)) (.lit 1)) (.var 27)) (.var 25)) (.var 22))))
    (.mul (.var powerN) (.var roundD))
def upperNegativeExpr : AE := .mul (.mul (.var powerK) (.var 32)) (.var 26)

def lowerAssignments : List Assignment :=
  [(roundD, denominatorExpr), (roundX, lowerPositiveExpr), (roundY, lowerNegativeExpr)]
def upperAssignments : List Assignment :=
  [(roundX, upperPositiveExpr), (roundY, upperNegativeExpr)]

theorem lowerAssignments_legal : assignmentsLegal lowerAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, lowerAssignments, denominatorExpr, lowerPositiveExpr, lowerNegativeExpr,
    AE.vars_ok, roundD, roundX, roundY, powerK, vZ, v1, v2, vPOS, VV]

theorem upperAssignments_legal : assignmentsLegal upperAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, upperAssignments, upperPositiveExpr, upperNegativeExpr,
    AE.vars_ok, roundD, roundX, roundY, powerK, powerN, vZ, v1, v2, vPOS, VV]

theorem lowerAssignments_cost : assignmentCost lowerAssignments ≤ 100 := by decide
theorem upperAssignments_cost : assignmentCost upperAssignments ≤ 100 := by decide

def Input.denominator (d : Input) : ℕ := d.Q * d.etaDen
def Input.lowerPositive (d : Input) : ℕ := 2 ^ d.k * d.A * d.etaDen
def Input.lowerNegative (d : Input) : ℕ := 2 ^ d.k * 2 * d.MF * d.nc * d.etaNum * d.Q
def Input.upperPositive (d : Input) : ℕ :=
  2 ^ d.k * (d.A * d.etaDen + (2 * d.MF + 1) * d.nc * d.etaNum * d.Q) +
    2 ^ d.n * d.denominator
def Input.upperNegative (d : Input) : ℕ := 2 ^ d.k * d.M * d.etaDen

theorem lowerAssignments_eval (d : Input) (env : Fin VV → ℕ) (hs : d.Stored env)
    (hk : env powerK = 2 ^ d.k) :
    assignmentEnv lowerAssignments env roundD = d.denominator ∧
      assignmentEnv lowerAssignments env roundX = d.lowerPositive ∧
      assignmentEnv lowerAssignments env roundY = d.lowerNegative := by
  obtain ⟨_, _, hQ, hMF, _, hNum, hDen, hnc, _, _, hA, _, _⟩ := hs
  simp (config := { decide := true }) [assignmentEnv, lowerAssignments, denominatorExpr,
    lowerPositiveExpr, lowerNegativeExpr, AE.eval, hQ, hMF, hNum, hDen, hnc, hA,
    hk, Input.denominator, Input.lowerPositive, Input.lowerNegative]

theorem upperAssignments_eval (d : Input) (env : Fin VV → ℕ) (hs : d.Stored env)
    (hn : env powerN = 2 ^ d.n) (hk : env powerK = 2 ^ d.k)
    (hD : env roundD = d.denominator) :
    assignmentEnv upperAssignments env roundX = d.upperPositive ∧
      assignmentEnv upperAssignments env roundY = d.upperNegative := by
  obtain ⟨_, _, hQ, hMF, _, hNum, hDen, hnc, _, _, hA, _, hM⟩ := hs
  simp (config := { decide := true }) [assignmentEnv, upperAssignments,
    upperPositiveExpr, upperNegativeExpr, AE.eval, hQ, hMF, hNum, hDen, hnc, hA, hM,
    hn, hk, hD, Input.upperPositive, Input.upperNegative]

theorem lowerNumeratorProgram_spec {C : Ctx} (d : Input) (a : DS VV)
    (hc : Cst a) (hs : d.Stored a.env) (hk : a.env powerK = 2 ^ d.k)
    (hcap : assignmentsSafe C.Wd lowerAssignments a.env) :
    Hs C (assignmentProgram lowerAssignments) a (assignmentCost lowerAssignments) (fun b =>
      b.env roundD = d.denominator ∧ b.env roundX = d.lowerPositive ∧
      b.env roundY = d.lowerNegative ∧
      lowAgree (assignmentEnv lowerAssignments a.env) b.env ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  refine Hs.mono (assignmentProgram_spec lowerAssignments lowerAssignments_legal a hc hcap) le_rfl ?_
  rintro b ⟨he, hp, hw, ho, hbc⟩
  have hv := lowerAssignments_eval d a.env hs hk
  exact ⟨(he roundD (by decide) (by decide)).trans hv.1,
    (he roundX (by decide) (by decide)).trans hv.2.1,
    (he roundY (by decide) (by decide)).trans hv.2.2, he, hp, hw, ho, hbc⟩

theorem upperNumeratorProgram_spec {C : Ctx} (d : Input) (a : DS VV)
    (hc : Cst a) (hs : d.Stored a.env) (hn : a.env powerN = 2 ^ d.n)
    (hk : a.env powerK = 2 ^ d.k) (hD : a.env roundD = d.denominator)
    (hcap : assignmentsSafe C.Wd upperAssignments a.env) :
    Hs C (assignmentProgram upperAssignments) a (assignmentCost upperAssignments) (fun b =>
      b.env roundX = d.upperPositive ∧ b.env roundY = d.upperNegative ∧
      lowAgree (assignmentEnv upperAssignments a.env) b.env ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  refine Hs.mono (assignmentProgram_spec upperAssignments upperAssignments_legal a hc hcap) le_rfl ?_
  rintro b ⟨he, hp, hw, ho, hbc⟩
  have hv := upperAssignments_eval d a.env hs hn hk hD
  exact ⟨(he roundX (by decide) (by decide)).trans hv.1,
    (he roundY (by decide) (by decide)).trans hv.2, he, hp, hw, ho, hbc⟩

end NearQuarticWires.StageOutput
