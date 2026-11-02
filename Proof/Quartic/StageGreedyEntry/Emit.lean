import Proof.Gates.Recovery.HTParts
import Proof.Gates.Codec.PairFrame

/-!
# Fixed bit lists and marked unary frames

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`emitList` appends a fixed list of bits (`emitList_exec`). `unaryMarksP v` appends the marked image
`marks (frame (1^m))` of a unary frame from a counter `v = m` and clears the counter
(`unaryMarks_exec`), in time linear in `m`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-- `lem:print`, paper/paper.tex: append the bits of `l`. -/
def emitList (o : Fin (ns+1)) (OP : Fin nr) : List Bool→WM ns nr
  | []=>.skip
  | b::l=>.seq (emitC o OP b) (emitList o OP l)

theorem emitList_exec (o : Fin (ns+1)) (OP : Fin nr) :
    ∀ (l : List Bool) (σ : WState ns nr),σ.sh o=(σ.st o).length → σ.val OP+l.length≤cap →
      WExec cap (emitList o OP l) σ (appendO σ o OP l) (8*l.length)
  | [],σ,_,_=>by
    rw [appendO_nil];exact WExec.skip σ
  | b::l,σ,ho,hc=>by
    have e1:=NearCubicGates.Close.Recovery.HTParts.emits_raw cap (dst:=o) (OP:=OP) b σ ho
      (by simp at hc ⊢;omega)
    have e2:=emitList_exec o OP l (appendO σ o OP [b]) (by simp [ho]) (by simp at hc ⊢;omega)
    rw [appendO_append] at e2
    exact WExec.mono (WExec.seq e1 e2) (by simp;omega)

/-- The marked image of a unary frame. -/
theorem marks_frame_ones : ∀ m : ℕ,
    marks (frame (List.replicate m true))=(List.replicate m [true,true,true,true]).flatten++[true,false]
  | 0=>by rw [NearCubicGates.Close.Codec.frame_eq_marks];rfl
  | m+1=>by
    have h : frame (List.replicate (m+1) true)=[true,true]++frame (List.replicate m true) := by
      rw [NearCubicGates.Close.Codec.frame_eq_marks,NearCubicGates.Close.Codec.frame_eq_marks]
      simp [List.replicate_succ,marks]
    rw [h,NearCubicWires.RepairOrdinary.Streaming.marks_append,marks_frame_ones m,List.replicate_succ,
      List.flatten_cons]
    rfl

/-- `lem:print`, paper/paper.tex: `marks (frame (1^v))`, clearing `v`. -/
def unaryMarksP (v : Fin nr) (o : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (.whr v (.seq (.dec v) (emitList o OP [true,true,true,true]))) (emitList o OP [true,false])

theorem unaryLoop_exec (v : Fin nr) (o : Fin (ns+1)) (OP : Fin nr) (hvO : v≠OP) :
    ∀ (m : ℕ) (σ : WState ns nr),σ.val v=m → m≤cap → σ.sh o=(σ.st o).length → σ.val OP+4*m≤cap →
      WExec cap (.whr v (.seq (.dec v) (emitList o OP [true,true,true,true]))) σ
        (appendO (σ.setv v 0) o OP (List.replicate m [true,true,true,true]).flatten) (36*m+1)
  | 0,σ,hv,_,_,_=>by
    have e : appendO (σ.setv v 0) o OP (List.replicate 0 [true,true,true,true]).flatten=σ := by
      rw [List.replicate_zero,List.flatten_nil,appendO_nil,←hv];exact wsetv_same σ v
    rw [e];exact WExec.whrF hv
  | m+1,σ,hv,hm,ho,hc=>by
    have d1:=WExec.dec (cap:=cap) v σ (by omega)
    set σ1:=σ.setv v (σ.val v-1) with hσ1
    have e1:=emitList_exec cap o OP [true,true,true,true] σ1 (by simp [hσ1,ho])
      (by simp [hσ1,Function.update_of_ne hvO.symm];omega)
    set σ2:=appendO σ1 o OP [true,true,true,true] with hσ2
    have ih:=unaryLoop_exec v o OP hvO m σ2 (by simp [hσ2,hσ1,Function.update_of_ne hvO,hv]) (by omega)
      (by simp [hσ2,hσ1,ho]) (by simp [hσ2,hσ1,Function.update_of_ne hvO.symm];omega)
    have e : appendO (σ2.setv v 0) o OP (List.replicate m [true,true,true,true]).flatten=
        appendO (σ.setv v 0) o OP (List.replicate (m+1) [true,true,true,true]).flatten := by
      rw [List.replicate_succ,List.flatten_cons,←appendO_append]
      congr 1
      refine WState.eq rfl rfl ?_ rfl
      funext x
      by_cases x1 : x=v
      · subst x1;simp [hσ2,hσ1,Function.update_of_ne hvO]
      · by_cases x2 : x=OP
        · subst x2;simp [hσ2,hσ1,Function.update_of_ne x1]
        · simp [hσ2,hσ1,Function.update_of_ne x1,Function.update_of_ne x2]
    rw [e] at ih
    exact WExec.mono (WExec.whrT (by omega) (WExec.seq d1 e1) ih) (by simp;omega)

theorem unaryMarks_exec (v : Fin nr) (o : Fin (ns+1)) (OP : Fin nr) (hvO : v≠OP)
    (m : ℕ) (σ : WState ns nr) (hv : σ.val v=m) (hm : m≤cap) (ho : σ.sh o=(σ.st o).length)
    (hc : σ.val OP+4*m+2≤cap) :
    WExec cap (unaryMarksP v o OP) σ (appendO (σ.setv v 0) o OP (marks (frame (List.replicate m true))))
      (36*m+18) := by
  have e1:=unaryLoop_exec cap v o OP hvO m σ hv hm ho (by omega)
  have e2:=emitList_exec cap o OP [true,false]
    (appendO (σ.setv v 0) o OP (List.replicate m [true,true,true,true]).flatten)
    (by simp [ho]) (by simp [Function.update_of_ne hvO.symm];omega)
  rw [appendO_append,←marks_frame_ones] at e2
  exact WExec.mono (WExec.seq e1 e2) (by simp)

end NearQuarticWires.StageGreedyEntry
