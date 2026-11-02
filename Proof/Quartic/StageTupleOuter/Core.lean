import Proof.Quartic.StageTupleOuter.Kernel
import Proof.Quartic.StageTupleOuter.Lift
import Proof.Quartic.StageTupleOuter.Exact
import Proof.Gates.Recovery.HTParts
import Proof.Gates.Expand.PolyTabPack
import Proof.Quartic.Program.Pipe

/-!
# The cold tuple printer

Paper: `lem:print` and `prop:time`, paper/paper.tex.

The core program runs the kernel (`kernelProg`) renamed into a layout with one more, fresh, output stream, then copies
the signed cut stream: it duplicates the physical emitted-byte counter (register 18), rewinds the cut tape (tape 21) by
it, copies exactly that many bits through the outer-frame markers onto the fresh stream, and writes the end marker
(`core_run`). The cut tape reads like the requested output (`SimW`); the copy is run on a surrogate holding it exactly
and transferred (`wexec_sim_eq`), so the fresh stream ends holding exactly `frame r.output`. `coreWF M` packages the
core with its final rewind (`Expand.PolyTab.wordFunction_of_ideal`); **`termCutWordFunction M setup`** pipes the
preparation `setup` into it.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (addTo addTo_spec)
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Expand.PolyTab (idealStart wordFunction_of_ideal)
open StageTuple

variable {B : StageNativeKids.NativeKidsRequest → ℕ}
  {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
    StageNativeKids.NativeKidsRequest.output B}
  {nativePrice : NativeStagePrice B}

/-- The fresh output stream and the cut tape, in the layout with one more stream. -/
def cOUT (span : ℕ) : Fin (span + 30 + 1) := Fin.last (span + 30)
def c21 (span : ℕ) : Fin (span + 30 + 1) := ⟨21, by omega⟩

/-- **The copy of the signed cut stream.** -/
def copyP (span : ℕ) : WM (span + 30) 32 :=
  .seq (addTo 18 24 26) (.seq (WM.rewind (c21 span) 18)
    (.seq (cntLoop (c21 span) 28 24 (fun b => emitPair (cOUT span) 27 b)) (emitC (cOUT span) 27 false)))

/-- **The core program.** -/
noncomputable def coreP (M : TermStageMachine native nativePrice) : WMX (M.span + 30) 32 :=
  .seq (WMX.liftX Fin.castSucc id (kernelProg M)) (.wm (copyP M.span))

/-- The blank workspace of the loader, on tape 13. -/
def coreLens (r : TermCutRequest) (span : ℕ) (i : Fin (span + 30 + 1)) : ℕ :=
  if i.val = 13 then r.preparedLoadCapacity else 0

/-- The core's capacity. -/
def coreCap (M : TermStageMachine native nativePrice) (r : TermCutRequest) : ℕ :=
  kernelCap M r + 3 * r.output.length + 10

/-- **The run of the core program.** -/
theorem core_run (M : TermStageMachine native nativePrice) (r : TermCutRequest) :
    ∃ τ, WXExec (coreCap M r) (coreP M) (idealStart (M.span + 30) 32 r.preparedWord (coreLens r M.span)) τ
        (tupleCoreCost M r) ∧ τ.st (cOUT M.span) = frame r.output := by
  set span := M.span with hspan
  set cap := coreCap M r with hcapd
  set σ0 := idealStart (span + 30) 32 r.preparedWord (coreLens r span) with hσ0
  -- the kernel, renamed
  obtain ⟨τk, ek, sk⟩ := kernel_run M r cap (by simp only [hcapd, coreCap]; omega)
  have hl0 : LiftW (Fin.castSucc : Fin (span + 29 + 1) → Fin (span + 30 + 1)) id σ0 (kernelStart span r) := by
    refine ⟨fun i => rfl, fun i => ?_, fun _ => rfl, rfl⟩
    show (if (Fin.castSucc i).val = 0 then frame r.preparedWord else
      List.replicate (coreLens r span (Fin.castSucc i)) false) = _
    simp only [kernelStart, Fin.val_castSucc, coreLens]
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h13 : i.val = 13 <;> simp [h0, h13]
  obtain ⟨ω1, e1, l1, o1⟩ := WXExec.liftX cap Fin.castSucc (Fin.castSucc_injective _) id Function.injective_id ek
    σ0 hl0
  -- facts at the end of the Terms loop
  have hOfar : ∀ i : Fin (span + 29 + 1), Fin.castSucc i ≠ cOUT span := fun i h => by
    have := congrArg Fin.val h; simp [cOUT] at this; omega
  have g1O : ω1.st (cOUT span) = [] ∧ ω1.sh (cOUT span) = 0 := by
    obtain ⟨hs, ht⟩ := o1.1 (cOUT span) hOfar
    refine ⟨?_, by rw [hs]; rfl⟩
    rw [ht]
    show (if (cOUT span).val = 0 then frame r.preparedWord else
      List.replicate (coreLens r span (cOUT span)) false) = []
    simp [cOUT, coreLens]
  have h21 : c21 span = Fin.castSucc (⟨21, by omega⟩ : Fin (span + 29 + 1)) := rfl
  have g1v : ∀ q : Fin 32, ω1.val q = ((r.progressData r.terms.length).state span r).val q := by
    intro q; rw [show ω1.val q = ω1.val (id q) from rfl, l1.val q, sk.val]
  have g1st : RdEq r.output (ω1.st (c21 span)) := by
    rw [h21, l1.st]
    have := sk.st ⟨21, by omega⟩
    simpa [KernelData.state, r.progressData_output] using this
  have g1sh : ω1.sh (c21 span) = r.output.length := by
    rw [h21, l1.sh, sk.sh]
    simp [KernelData.state, r.progressData_output]
  have g18 : ω1.val 18 = r.output.length := by
    rw [g1v]; simp [KernelData.state, r.progressData_output]
  have gz : ∀ q : Fin 32, 19 ≤ q.val → ω1.val q = 0 := by
    intro q hq; rw [g1v]
    simp only [KernelData.state]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- the surrogate holding the cut stream exactly
  set ω1s := ω1.sets (c21 span) r.output with hω1s
  have sim1 : SimW ω1s ω1 := by
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    by_cases hi : i = c21 span
    · subst hi; simpa [hω1s] using g1st
    · simp only [hω1s, WState.sets_st, Function.update_of_ne hi]; exact RdEq.refl _
  have hOc : cOUT span ≠ c21 span := fun h => by have := congrArg Fin.val h; simp [cOUT, c21] at this
  -- the copy on the surrogate
  have hcap := hcapd
  have hcp : r.output.length ≤ cap := by simp only [hcapd, coreCap]; omega
  have x1 := addTo_spec cap (18 : Fin 32) 24 26 (by decide) (by decide) (by decide) ω1s
    (by simp [hω1s]; exact gz 26 (by decide)) (by simp [hω1s, g18]; exact hcp)
    (by simp [hω1s, g18, gz 24 (by decide)]; exact hcp)
  set ω2 := ω1s.setv 24 (ω1s.val 24 + ω1s.val 18) with hω2
  have v2 : ω2.val 24 = r.output.length := by simp [hω2, hω1s, g18, gz 24 (by decide)]
  have x2 := wrewind_spec cap (c21 span) (18 : Fin 32) r.output.length ω2
    (by simp [hω2, hω1s, g18]) (by simp [hω2, hω1s, g18]; exact hcp)
  set ω3 := (ω2.setv 18 0).seth (c21 span) (ω2.sh (c21 span) - r.output.length) with hω3
  have x3 := cntLoop_spec cap (src := c21 span) (dst := cOUT span) (OP := (27 : Fin 32)) (SC := 28) (K := 24)
    (Ne.symm hOc) (by decide) (by decide) (by decide) (emits_pair cap) [] r.output [] ω3
    (by simp [hω3, hω2, hω1s]) (by simp [hω3, hω2, hω1s, g1sh])
    (by simp [hω3, hω2, hω1s, Function.update_of_ne hOc, g1O.1, g1O.2])
    (by simp [hω3, hω2]; exact v2) hcp
    (by
      have : (r.output.flatMap fun b => [true, b]).length = 2 * r.output.length := by
        rw [show (r.output.flatMap fun b => [true, b]) = marks r.output from rfl, Streaming.marks_length]
      simp [hω3, hω2, hω1s, gz 27 (by decide)]
      simp only [hcapd, coreCap]; omega)
    (by simp [hω3, hω2, hω1s, gz 28 (by decide)]; simp only [hcapd, coreCap]; omega)
  set ω4 := (adv (c21 span) (cOUT span) 27 28 ω3 (r.output.flatMap fun b => [true, b]) r.output.length).setv 24 0
    with hω4
  have hm : (r.output.flatMap fun b => [true, b]) = marks r.output := rfl
  have x4 := emitC_spec cap (cOUT span) (27 : Fin 32) false ω4
    (by simp [hω4, adv, appendO, hω3, hω2, hω1s, Function.update_of_ne hOc, g1O.1, g1O.2])
    (by
      simp [hω4, adv, appendO, hω3, hω2, hω1s, gz 27 (by decide), hm, Streaming.marks_length]
      simp only [hcapd, coreCap]; omega)
  have ecopy : WExec cap (copyP span) ω1s
      (((ω4.sets (cOUT span) (ω4.st (cOUT span) ++ [false])).seth (cOUT span) (ω4.sh (cOUT span) + 1)).setv 27
        (ω4.val 27 + 1))
      (18 * ω1s.val 18 + 3 + 1 + (5 * r.output.length + 1 + 1 +
        (r.output.length * (15 + 11) + 1 + 1 + 7))) := WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))
  -- transfer to the actual state
  obtain ⟨ω5, e5, _, h5⟩ := wexec_sim_eq (cOUT span) ecopy ω1 sim1
    (by simp [hω1s, Function.update_of_ne hOc])
  refine ⟨ω5, WXExec.mono (WXExec.seq e1 (WXExec.wm e5)) ?_, ?_⟩
  · have hv : ω1s.val 18 = r.output.length := by simp [hω1s, g18]
    rw [hv]; unfold tupleCoreCost; omega
  · rw [h5]
    simp [hω4, adv, appendO, hω3, hω2, hω1s, Function.update_of_ne hOc, g1O.1, hm]
    rw [NearCubicGates.Close.Codec.frame_eq_marks]

/-- **The core word function**: the prepared word to the framed signed cut stream, with its final rewind. -/
noncomputable def coreWF (M : TermStageMachine native nativePrice) :
    WordFunction TermCutRequest TermCutRequest.preparedWord (fun r => frame r.output)
      (fun r => 2 * tupleCoreCost M r + 2) :=
  wordFunction_of_ideal (coreP M) (cOUT M.span) (by simp [cOUT]) (coreCap M) (fun r => coreLens r M.span)
    (tupleCoreCost M) (fun _ => le_refl _) (fun r => ⟨by simp [coreLens, cOUT], core_run M r⟩)

/-- **The cold tuple printer** (`lem:print`, paper/paper.tex): the preparation `setup`, then the
core, each once. -/
noncomputable def termCutWordFunction (M : TermStageMachine native nativePrice) {Bs : TermCutRequest → ℕ}
    (setup : WordFunction TermCutRequest TermCutRequest.word (fun r => frame r.preparedWord) Bs) :
    WordFunction TermCutRequest TermCutRequest.word (fun r => frame r.output) (termCutBudget M Bs) :=
  Program.WordFunction.pipe setup (coreWF M)

end NearQuarticWires.StageTupleOuter
