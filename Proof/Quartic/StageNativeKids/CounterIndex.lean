import Proof.Quartic.StagePrintTuple.UnaryField
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
actual current original-child index is copied to a scratch register and
emitted in the existing nested unary row-call field, preserving the
persistent loop index and clearing both scratch registers. -/
def copyNestedIndex (A K T : Fin nr) (dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (wcopyR A K T) (emitNestedUnary K dst OP)

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual nested unary child-index bit
is physically printed from the computed loop register, with its full
copy and marker clock and no supplied index tape. -/
theorem copyNestedIndex_spec (cap : ℕ) (A K T : Fin nr) (dst : Fin (ns + 1))
    (OP : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP)
    (σ : WState ns nr) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (hd : σ.sh dst = (σ.st dst).length) (hj : σ.val A ≤ cap)
    (hcap : σ.val OP + 8 * σ.val A + 8 ≤ cap) :
    WExec cap (copyNestedIndex A K T dst OP) σ
      (appendO σ dst OP (marks (frame (frame (List.replicate (σ.val A) true)))))
      (120 * (σ.val A + 1)) := by
  have e1 := wcopyR_spec cap A K T hAK hAT hKT σ hK hT hj
  let d := σ.setv K (σ.val A)
  have e2 := emitNestedUnary_spec cap K dst OP hKO (σ.val A) d
    (by simp [d]) (by simpa [d] using hd) hj
    (by simpa [d, Function.update_of_ne hKO.symm] using hcap)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext i
    by_cases hi : i = K
    · subst i; simp [d, appendO, hKO, hK]
    · by_cases ho : i = OP
      · subst i; simp [d, appendO, hKO.symm]
      · simp [d, appendO, Function.update_of_ne hi, Function.update_of_ne ho, hKO.symm]
  · rfl

end NearQuarticWires.StageNativeKids
