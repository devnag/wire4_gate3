import Proof.Gates.CounterAsm.Copy
import Proof.Gates.Expand.PolyTabPack

/-!
# Preparing the binary arithmetic input

Paper: `prop:time`, paper/paper.tex. A linear pass puts the
Step 5 scalar word into the two-frame input format of the binary arithmetic
machine. The second frame is empty. Every marker and payload bit is written
by the ordinary machine, with a linear running-time bound.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Expand.PolyTab

/-- The scalar input and an empty auxiliary input. -/
def arithmeticInput (w : List Bool) : List Bool := frame w ++ frame []

/-- Write the framed arithmetic input by a single scan of the original frame. -/
def arithmeticFrameProgram : WMX 1 2 := .wm
  (.seq (CounterAsm.frameCopy 0 1 (fun b => emitPair 1 0 b))
    (.seq (emitPair 1 0 false) (emitC 1 0 false)))

theorem arithmeticFrame_run (w : List Bool) :
    ∃ τ, WXExec (4 * w.length + 5) arithmeticFrameProgram
      (idealStart 1 2 w (fun _ => 0)) τ (110 * w.length + 79) ∧
      τ.st 1 = frame (arithmeticInput w) := by
  let σ := idealStart 1 2 w (fun _ => 0)
  let u := (frame w).flatMap (fun b => [true, b])
  have hfl : (frame w).length = 2 * w.length + 1 := by
    rw [Codec.frame_eq_marks]
    simp
  have hul : u.length = 4 * w.length + 2 := by
    dsimp [u]
    rw [List.length_flatMap]
    simp only [List.length_cons, List.length_nil, Nat.zero_add, List.map_const',
      List.sum_replicate, smul_eq_mul]
    omega
  have hcopy := CounterAsm.frameCopy_spec (4 * w.length + 5)
    (src := (0 : Fin 2)) (dst := (1 : Fin 2)) (OP := (0 : Fin 2)) (SC := (1 : Fin 2))
    (by decide) (by decide) (emits_pair _) (d := 2) (by intro b; simp)
    w [] [] σ (by simp [σ, idealStart]) rfl rfl
    (by simp only [σ, idealStart]; omega) (by simp only [σ, idealStart]; omega)
  let σ1 := adv (0 : Fin 2) 1 0 1 σ u (frame w).length
  have hs1 : σ1.st 1 = u := by simp [σ1, σ, idealStart]
  have hh1 : σ1.sh 1 = u.length := by
    rw [show σ1 = adv (0 : Fin 2) 1 0 1 σ u (frame w).length from rfl,
      adv_sh_dst (by decide)]
    simp [σ, idealStart]
  have hv1 : σ1.val 0 = u.length := by
    rw [show σ1 = adv (0 : Fin 2) 1 0 1 σ u (frame w).length from rfl,
      adv_val_OP (by decide)]
    simp [σ, idealStart]
  have hpair := emitPair_spec (4 * w.length + 5) (1 : Fin 2) (0 : Fin 2) false σ1
    (by rw [hh1, hs1]) (by rw [hv1, hul]; omega)
  let σ2 := appendO σ1 (1 : Fin 2) 0 [true, false]
  have hlast := Codec.emitBit_spec (4 * w.length + 5) (1 : Fin 2) (0 : Fin 2) false σ2
    (by simp [σ2, appendO, hh1, hs1])
    (by simp [σ2, appendO, hv1, hul])
  refine ⟨appendO σ2 (1 : Fin 2) 0 [false],
    WXExec.mono (WXExec.wm (WExec.seq hcopy (WExec.seq hpair hlast))) (by rw [hfl]; omega), ?_⟩
  simp only [σ2, appendO, WState.setv_st, WState.seth_st, WState.sets_st,
    Function.update_self, hs1]
  change u ++ [true, false] ++ [false] = frame (frame w ++ frame [])
  rw [Codec.frame_eq_marks]
  simp only [frame, Streaming.marks_append]
  rfl

/-- A uniform ordinary machine writes both input frames, including the outer handoff frame. -/
noncomputable def arithmeticFraming :
    WordFunction (List Bool) id (fun w => frame (arithmeticInput w))
      (fun w => 400 * (w.length + 1)) :=
  wordFunction_of_ideal arithmeticFrameProgram 1 (by decide)
    (fun w => 4 * w.length + 5) (fun _ _ => 0)
    (fun w => 110 * w.length + 79) (by intro w; omega)
    (by intro w; exact ⟨rfl, arithmeticFrame_run w⟩)

end NearQuarticWires.StageOutput
