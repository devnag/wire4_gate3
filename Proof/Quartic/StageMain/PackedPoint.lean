import Proof.Quartic.StageOutput.Preservation

/-!
# Reading a packed input point one coordinate at a time

Paper: `sec:algorithm`, paper/paper.tex, and
`def:class`. The input coordinates of a threshold gate
are read in increasing order from a binary packed point. A division by two
retains the unread suffix and the remainder is the next Boolean coordinate.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch
open StageOutput

def pointWork : Fin VV := ⟨40, by decide⟩
def pointSaved : Fin VV := ⟨41, by decide⟩
def scorePositive : Fin VV := ⟨42, by decide⟩
def scoreNegative : Fin VV := ⟨43, by decide⟩
def weightIndex : Fin VV := ⟨44, by decide⟩
def weightLength : Fin VV := ⟨45, by decide⟩
def pointBit : Fin VV := ⟨46, by decide⟩

def nextBitAssignments : List Assignment :=
  [(pointBit, .sub (.var pointWork) (.mul (.lit 2) (.div (.var pointWork) (.lit 2)))),
   (pointWork, .div (.var pointWork) (.lit 2))]

def nextPointBit : St VV := assignmentProgram nextBitAssignments

theorem nextBitAssignments_legal : assignmentsLegal nextBitAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, nextBitAssignments,
    AE.vars_ok, pointBit, pointWork, vZ, v1, v2, vPOS, VV]

theorem nextBitAssignments_safe (W : ℕ) (env : Fin VV → ℕ)
    (hW : 2 ≤ W) (hvalue : env pointWork < 2 ^ W) :
    assignmentsSafe W nextBitAssignments env := by
  have hfour : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hprodle : 2 * (env pointWork / 2) ≤ env pointWork := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (env pointWork) 2
  have hprod : 2 * (env pointWork / 2) < 2 ^ W := hprodle.trans_lt hvalue
  simpa (config := { decide := true }) [assignmentsSafe, nextBitAssignments, AE.ok, AE.eval]
    using (show (True ∧ ((2 < 2 ^ W) ∧ (True ∧ 2 < 2 ^ W ∧ 0 < 2 ∧ 2 * 2 ≤ 2 ^ W) ∧
      2 * (env pointWork / 2) < 2 ^ W)) ∧
      (True ∧ 2 < 2 ^ W ∧ 0 < 2 ∧ 2 * 2 ≤ 2 ^ W) ∧ True from
      ⟨⟨trivial, by omega, ⟨trivial, by omega, by omega, by omega⟩, hprod⟩,
       ⟨trivial, by omega, by omega, by omega⟩, trivial⟩)

/-- The actual binary arithmetic program advances one coordinate. -/
theorem nextPointBit_spec {C : Ctx} (a : DS VV) (hc : Cst a)
    (hW : 2 ≤ C.Wd) (hvalue : a.env pointWork < 2 ^ C.Wd) :
    Hs C nextPointBit a 50 (fun b =>
      b.env pointBit = a.env pointWork % 2 ∧ b.env pointWork = a.env pointWork / 2 ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [vJ, pointBit, pointWork]) := by
  refine Hs.mono (assignmentProgram_spec nextBitAssignments nextBitAssignments_legal a hc
    (nextBitAssignments_safe C.Wd a.env hW hvalue)) (by decide) ?_
  rintro b ⟨be, bp, bw, bo, bc⟩
  refine ⟨?_, ?_, bp, bw, bo, bc, assignmentProgram_frame be⟩
  · rw [be pointBit (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, nextBitAssignments, AE.eval]
    have := Nat.mod_add_div (a.env pointWork) 2
    omega
  · rw [be pointWork (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, nextBitAssignments, AE.eval]

end NearQuarticWires.StageMain
