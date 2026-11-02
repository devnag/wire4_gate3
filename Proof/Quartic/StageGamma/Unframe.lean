import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.FinalPassWordAux
import Proof.Wire_3_5.PrimAsmWriteNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ} (cap : ℕ)

/-- `cor:conditional`, paper/paper.tex: a marked input
pair contributes its data bit to a Gaussian input tape. -/
def unframePair (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.fwd src)
    (.seq (.ifs src (emitC dst OP true) (emitC dst OP false)) (.fwd src))

/-- `cor:conditional`, paper/paper.tex: decode one
self-delimiting tape record, consume its delimiter and rewind the output. -/
def unframeRecord (src dst : Fin (ns + 1)) (OP : Fin nr) : WM ns nr :=
  .seq (.whs src (unframePair src dst OP)) (.seq (.fwd src) (WM.rewind dst OP))

/-- `cor:conditional`, paper/paper.tex: the actual
copy loop advances only across this record's marked pairs. -/
theorem unframe_loop (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP : Fin nr)
    (rest : List Bool) : ∀ (bits pre : List Bool) (σ : WState ns nr),
    σ.st src = pre ++ frame bits ++ rest → σ.sh src = pre.length →
    σ.sh dst = (σ.st dst).length → σ.val OP + bits.length ≤ cap →
    WExec cap (.whs src (unframePair src dst OP)) σ
      ((appendO σ dst OP bits).seth src (pre.length + 2 * bits.length))
      (18 * bits.length + 1)
  | [], pre, σ, hst, hsh, _, _ => by
    have hb : wbit σ src = false := by
      unfold wbit readTapeBit
      rw [hst, hsh]
      simp [frame, List.getD_append_right]
    have e : (appendO σ dst OP []).seth src (pre.length + 2 * ([] : List Bool).length) = σ := by
      apply WState.eq
      · funext y
        by_cases hy : y = src
        · subst hy; simp [appendO, hsd, hsh]
        · by_cases hyd : y = dst
          · subst hyd; simp [appendO, Function.update_apply, hy]
          · simp [appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
      · simp [appendO]
      · simp [appendO]
      · rfl
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp)
  | bit :: bits, pre, σ, hst, hsh, hd, hc => by
    have hb : wbit σ src = true := by
      unfold wbit readTapeBit
      rw [hst, hsh]
      simp [frame, List.getD_append_right]
    have e1 := WExec.fwd (cap := cap) src σ
    let σ1 := σ.seth src (σ.sh src + 1)
    have hdata : wbit σ1 src = bit := by
      unfold wbit readTapeBit
      simp only [σ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hst, hsh]
      simp [frame, List.getD_append_right]
    have hd1 : σ1.sh dst = (σ1.st dst).length := by
      simp [σ1, Function.update_of_ne hsd.symm, hd]
    have hc1 : σ1.val OP < cap := by simp [σ1]; simp at hc; omega
    have e2 : WExec cap (.ifs src (emitC dst OP true) (emitC dst OP false)) σ1
        (((σ1.sets dst (σ1.st dst ++ [bit])).seth dst (σ1.sh dst + 1)).setv OP (σ1.val OP + 1)) 8 := by
      cases bit
      · exact WExec.mono (WExec.ifsF hdata (emitC_spec cap dst OP false σ1 hd1 hc1)) (by omega)
      · exact WExec.mono (WExec.ifsT hdata (emitC_spec cap dst OP true σ1 hd1 hc1)) (by omega)
    let σ2 := ((σ1.sets dst (σ1.st dst ++ [bit])).seth dst (σ1.sh dst + 1)).setv OP (σ1.val OP + 1)
    have e3 := WExec.fwd (cap := cap) src σ2
    let σ3 := σ2.seth src (σ2.sh src + 1)
    have ih := unframe_loop src dst hsd OP rest bits (pre ++ [true, bit]) σ3
      (by simp [σ3, σ2, σ1, Function.update_apply, hsd, hst, frame])
      (by simp [σ3, σ2, σ1, Function.update_apply, hsd, hsh])
      (by simp [σ3, σ2, σ1, Function.update_apply, hsd.symm, hd])
      (by simp [σ3, σ2, σ1]; simp at hc; omega)
    have e := WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih
    refine WExec.cast cap e ?_ (by simp; omega)
    apply WState.eq
    · funext y
      by_cases hy : y = src
      · subst hy; simp [σ3, σ2, σ1, appendO, hsd, hsh]; omega
      · by_cases hyd : y = dst
        · subst hyd; simp [σ3, σ2, σ1, appendO, Function.update_apply, hy]; omega
        · simp [σ3, σ2, σ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
    · funext y
      by_cases hyd : y = dst
      · subst hyd; simp [σ3, σ2, σ1, appendO, Function.update_apply, hsd.symm]
      · simp [σ3, σ2, σ1, appendO, Function.update_of_ne hyd]
    · funext r
      by_cases hr : r = OP
      · subst hr; simp [σ3, σ2, σ1, appendO]; omega
      · simp [σ3, σ2, σ1, appendO, Function.update_of_ne hr]
    · simp [σ3, σ2, σ1, appendO]

/-- `cor:conditional`, paper/paper.tex: every bit of a
record is loaded by physical transitions; the next record starts at its
first marker and the output head is restored to its original position. -/
theorem unframeRecord_run (src dst : Fin (ns + 1)) (hsd : src ≠ dst) (OP : Fin nr)
    (bits pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src = pre ++ frame bits ++ rest) (hsh : σ.sh src = pre.length)
    (hd : σ.sh dst = (σ.st dst).length) (hOP : σ.val OP = 0) (hc : bits.length ≤ cap) :
    WExec cap (unframeRecord src dst OP) σ
      ((σ.sets dst (σ.st dst ++ bits)).seth src (pre.length + 2 * bits.length + 1))
      (23 * bits.length + 5) := by
  have h1 := unframe_loop cap src dst hsd OP rest bits pre σ hst hsh hd (by omega)
  let σ1 := (appendO σ dst OP bits).seth src (pre.length + 2 * bits.length)
  have h2 := WExec.fwd (cap := cap) src σ1
  let σ2 := σ1.seth src (σ1.sh src + 1)
  have h3 := wrewind_spec cap dst OP bits.length σ2
    (by simp [σ2, σ1, appendO, hOP])
    (by simpa [σ2, σ1, appendO, hOP] using hc)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  apply WState.eq
  · funext y
    by_cases hy : y = src
    · subst hy; simp [σ2, σ1, appendO, hsd]
    · by_cases hyd : y = dst
      · subst hyd; simp [σ2, σ1, appendO, Function.update_apply, hy]
      · simp [σ2, σ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyd]
  · funext y
    by_cases hyd : y = dst
    · subst hyd; simp [σ2, σ1, appendO, Function.update_apply]
    · simp [σ2, σ1, appendO, Function.update_of_ne hyd]
  · funext r
    by_cases hr : r = OP
    · subst hr; simp [σ2, σ1, appendO, hOP]
    · simp [σ2, σ1, appendO, Function.update_of_ne hr]
  · rfl

end NearQuarticWires.StageGamma
