import Proof.Quartic.StageMain.Threshold
import Proof.Gates.Dispatch.WitnessA

/-!
# Appending one evaluated gate bit

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Bottom-gate values are stored in their
literal list order. A running power of two appends each value at its
coordinate; repeated occurrences remain distinct bits.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Counter
open NearCubicGates.Close.Dispatch
open StageOutput

def gateCount : Fin VV := ⟨50, by decide⟩
def gateIndex : Fin VV := ⟨51, by decide⟩
def gateBits : Fin VV := ⟨52, by decide⟩
def gatePower : Fin VV := ⟨53, by decide⟩

def appendGateAssignments : List Assignment :=
  [(gateBits, .add (.var gateBits) (.mul (.var gateResult) (.var gatePower))),
   (gatePower, .mul (.lit 2) (.var gatePower))]
def appendGateBit : St VV := assignmentProgram appendGateAssignments

theorem appendGateAssignments_legal : assignmentsLegal appendGateAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, appendGateAssignments,
    AE.vars_ok, gateBits, gatePower, gateResult, vZ, v1, v2, vPOS, VV]

theorem appendGateBit_spec {C : Ctx} (a : DS VV) (hc : Cst a) (bs : List Bool) (bit : Bool)
    (hbits : a.env gateBits = bitsValue bs) (hpower : a.env gatePower = 2 ^ bs.length)
    (hbit : a.env gateResult = bit.toNat) (hW : bs.length + 2 ≤ C.Wd) :
    Hs C appendGateBit a 40 (fun b =>
      b.env gateBits = bitsValue (bs ++ [bit]) ∧ b.env gatePower = 2 ^ (bs.length + 1) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [vJ, gateBits, gatePower]) := by
  have hb := bitsValue_lt bs
  have hval : bit.toNat ≤ 1 := by cases bit <;> decide
  have hp : 0 < 2 ^ bs.length := by positivity
  have hcap : 4 * 2 ^ bs.length ≤ 2 ^ C.Wd := by
    have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hW
    simpa [pow_add, Nat.mul_comm] using this
  have hs : assignmentsSafe C.Wd appendGateAssignments a.env := by
    simp (config := { decide := true }) [assignmentsSafe, appendGateAssignments, AE.ok, AE.eval,
      hbits, hpower, hbit]
    constructor
    · constructor <;> nlinarith
    · constructor <;> nlinarith
  refine Hs.mono (assignmentProgram_spec appendGateAssignments appendGateAssignments_legal a hc hs)
    (by decide) ?_
  rintro b ⟨be, bp, bw, bo, bc⟩
  refine ⟨?_, ?_, bp, bw, bo, bc, assignmentProgram_frame be⟩
  · rw [be gateBits (by decide) (by decide), bitsValue_append]
    simp (config := { decide := true }) [assignmentEnv, appendGateAssignments, AE.eval,
      hbits, hpower, hbit, bitsValue, Nat.mul_comm]
  · rw [be gatePower (by decide) (by decide)]
    simp (config := { decide := true }) [assignmentEnv, appendGateAssignments, AE.eval,
      hpower, pow_succ, Nat.mul_comm]

end NearQuarticWires.StageMain
