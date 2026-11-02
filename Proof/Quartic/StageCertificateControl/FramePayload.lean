import Proof.Quartic.Control.Write
import Proof.Quartic.StagePrint.PoolLoop

/-!
# Append each counted cache payload without its outer frame

Paper: the whole native table in `lem:print`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearQuarticWires.Control
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- The sequential native table stream in `lem:print`,
paper/paper.tex, copies one actual framed cache
payload and consumes its outer terminal marker. -/
def copyPayload (src dst : Fin (ns+1)) (OP SC : Fin nr) : WMX ns nr :=
  .seq (Control.copyLoop false src dst OP SC) (WMX.fwd src)

/-- The actual cache payload copy of `lem:print` and `prop:time`,
paper/paper.tex, is driven by
frame markers. It requires only the source's read bits, retains the
exact destination tape, and charges every payload bit and delimiter. -/
theorem copyPayload_exec (cap : ℕ) (σ : WState ns nr)
    (src dst : Fin (ns+1)) (OP SC : Fin nr) (hsd : src≠dst) (hOS : OP≠SC)
    (payload rest : List Bool)
    (hread : ∀ q,readTapeBit (σ.st src) (σ.sh src+q)=readTapeBit (frame payload++rest) q)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : σ.val OP+4*payload.length+4≤cap)
    (hscan : σ.val SC+2*payload.length+2≤cap) :
    WXExec cap (copyPayload src dst OP SC) σ
      ((Control.copySt σ src dst OP SC payload.length (marks payload)).seth src
        (σ.sh src+2*payload.length+1)) (52*payload.length+3) := by
  have ec := Control.copyLoop_exec_read cap σ src dst OP SC false hsd hOS payload (false::rest)
    (fun q => by simpa only [Codec.frame_eq_marks,List.append_assoc,List.singleton_append] using hread q)
    (by rfl) hd hcap hscan
  rw [Control.bitCells_false] at ec
  let middle := Control.copySt σ src dst OP SC payload.length (marks payload)
  have ef := WXExec.fwd cap src middle
  refine (WXExec.seq ec ef).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst i
      simp [middle,Control.copySt,hsd]
    · simp only [middle,WState.seth_sh,Function.update_of_ne hi]
  · rfl
  · rfl
  · rfl

end NearQuarticWires.StageCertificateControl
