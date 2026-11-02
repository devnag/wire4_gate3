import Proof.Gates.Codec.Unframe

/-!
# Framed payload copying after a dispatch tag

Step 4 of `sec:algorithm`, paper/paper.tex, invokes
fixed ordinary subroutines on the sampled positions. A tagged call reads
its payload from the original source, writes every marked bit, and
rewinds the destination before entering the selected subroutine.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Codec

variable {ns nr : ℕ}

theorem copyFrame_prefix (cap : ℕ) (src dst : Fin (ns + 1)) (hsd : src ≠ dst)
    (OP : Fin nr) (pre x rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src = pre ++ frame x ++ rest) (hsh : σ.sh src = pre.length)
    (hd : σ.sh dst = (σ.st dst).length) (hc : σ.val OP + 2 * x.length + 1 ≤ cap) :
    WExec cap (copyFrameW src dst OP) σ
      ((appendO σ dst OP (frame x)).seth src (pre.length + 2 * x.length))
      (22 * x.length + 9) := by
  have e1 := copyFrame_loop cap src dst hsd OP rest x pre σ hst hsh hd (by omega)
  let σ1 := (appendO σ dst OP (marks x)).seth src (pre.length + 2 * x.length)
  have e2 := emitC_spec cap dst OP false σ1
    (by simp [σ1, appendO, Function.update_of_ne hsd.symm, hd, Streaming.marks_length])
    (by simp [σ1, appendO, Streaming.marks_length]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext y
    by_cases hy : y = src
    · subst hy; simp [σ1, appendO, hsd]
    · by_cases hyd : y = dst
      · subst hyd
        simp [σ1, appendO, hy, Streaming.marks_length, frame_eq_marks]
        omega
      · simp [σ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
  · funext y
    by_cases hy : y = dst
    · subst hy; simp [σ1, appendO, frame_eq_marks]
    · simp [σ1, appendO, Function.update_of_ne hy]
  · funext r
    by_cases hr : r = OP
    · subst hr; simp [σ1, appendO, Streaming.marks_length, frame_eq_marks]; omega
    · simp [σ1, appendO, Function.update_of_ne hr]
  · simp [σ1, appendO]

def copyPayload (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (copyFrameW src dst OP) (WM.rewind dst OP)

theorem copyPayload_run (cap : ℕ) (src dst : Fin (ns + 1)) (hsd : src ≠ dst)
    (OP : Fin nr) (pre x rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src = pre ++ frame x ++ rest) (hsh : σ.sh src = pre.length)
    (hd : σ.st dst = []) (hdh : σ.sh dst = 0) (hO : σ.val OP = 0)
    (hc : 2 * x.length + 2 ≤ cap) :
    WExec cap (copyPayload src dst OP) σ
      ((σ.sets dst (frame x)).seth src (pre.length + 2 * x.length))
      (32 * x.length + 16) := by
  have hfl : (frame x).length = 2 * x.length + 1 := frame_length x
  have e1 := copyFrame_prefix cap src dst hsd OP pre x rest σ hst hsh
    (by rw [hd, hdh]; rfl) (by omega)
  let σ1 := (appendO σ dst OP (frame x)).seth src (pre.length + 2 * x.length)
  have hO1 : σ1.val OP = 2 * x.length + 1 := by simp [σ1, appendO, hO, hfl]
  have e2 := wrewind_spec cap dst OP (2 * x.length + 1) σ1 hO1 (by omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext y
    by_cases hy : y = dst
    · subst hy; simp [σ1, appendO, Function.update_of_ne hsd.symm, hdh, hfl]
    · by_cases hys : y = src
      · subst hys; simp [σ1, appendO, hy]
      · simp [σ1, appendO, Function.update_of_ne hy, Function.update_of_ne hys]
  · funext y
    by_cases hy : y = dst
    · subst hy; simp [σ1, appendO, hd]
    · simp [σ1, appendO, Function.update_of_ne hy]
  · funext r
    by_cases hr : r = OP
    · subst hr; simp [σ1, appendO, hO]
    · simp [σ1, appendO, Function.update_of_ne hr]
  · simp [σ1, appendO]

end NearQuarticWires.StageMain.Tagged
