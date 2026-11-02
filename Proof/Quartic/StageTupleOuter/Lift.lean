import Proof.Gates.WordPrograms.WMX
import Proof.Wire_3_5.FinalPassLiftR

/-!
# Renaming the streams and registers of a word program with machine calls

Paper: `lem:print`, paper/paper.tex.

`WMX.liftX fs fr P` runs `P` on the streams `fs i` and the registers `fr r` of a larger layout (a docked machine
keeps its tapes, renamed by `fs`). `WXExec.liftX`: every run of `P` is a run of the renamed program that carries the
same streams, heads, registers and cell on the images, and leaves every stream and register outside the images
unchanged (`LiftW`, `OutsideW`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

variable {ns ns' nr nr' : ℕ}

/-- The renamed program. -/
def WMX.liftX (fs : Fin (ns + 1) → Fin (ns' + 1)) (fr : Fin nr → Fin nr') : WMX ns nr → WMX ns' nr'
  | .wm P => .wm (P.liftW fs fr)
  | .mach M tmap => .mach M (fs ∘ tmap)
  | .seq P Q => .seq (WMX.liftX fs fr P) (WMX.liftX fs fr Q)
  | .ifr r P Q => .ifr (fr r) (WMX.liftX fs fr P) (WMX.liftX fs fr Q)
  | .ifs i P Q => .ifs (fs i) (WMX.liftX fs fr P) (WMX.liftX fs fr Q)
  | .whr r P => .whr (fr r) (WMX.liftX fs fr P)
  | .whs i P => .whs (fs i) (WMX.liftX fs fr P)

theorem liftW_updS {t : ℕ} (fs : Fin (ns + 1) → Fin (ns' + 1)) (hfs : Function.Injective fs)
    (fr : Fin nr → Fin nr') (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap)
    {ω : WState ns' nr'} {σ : WState ns nr} (h : LiftW fs fr ω σ) (hout : Fin t → ℕ) (tout : Fin t → List Bool) :
    LiftW fs fr (updS (fs ∘ tmap) ω hout tout) (updS tmap σ hout tout) ∧
      OutsideW fs fr ω (updS (fs ∘ tmap) ω hout tout) := by
  have hc : Function.Injective (fs ∘ tmap) := hfs.comp hinj
  refine ⟨⟨fun i => ?_, fun i => ?_, fun r => ?_, ?_⟩, fun j hj => ?_, fun q _ => ?_⟩
  · by_cases hi : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [show fs (tmap j) = (fs ∘ tmap) j from rfl, updS_sh_slot _ ω hout tout hc, updS_sh_slot _ σ hout tout hinj]
    · have hi' : ∀ j, tmap j ≠ i := fun j hj => hi ⟨j, hj⟩
      have hi'' : ∀ j, (fs ∘ tmap) j ≠ fs i := fun j hj => hi' j (hfs hj)
      rw [updS_sh_other _ ω hout tout _ hi'', updS_sh_other _ σ hout tout _ hi', h.sh]
  · by_cases hi : ∃ j, tmap j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [show fs (tmap j) = (fs ∘ tmap) j from rfl, updS_st_slot _ ω hout tout hc, updS_st_slot _ σ hout tout hinj]
    · have hi' : ∀ j, tmap j ≠ i := fun j hj => hi ⟨j, hj⟩
      have hi'' : ∀ j, (fs ∘ tmap) j ≠ fs i := fun j hj => hi' j (hfs hj)
      rw [updS_st_other _ ω hout tout _ hi'', updS_st_other _ σ hout tout _ hi', h.st]
  · rw [updS_val, updS_val, h.val]
  · rw [updS_cell, updS_cell, h.cell]
  · have hj' : ∀ k, (fs ∘ tmap) k ≠ j := fun k hk => hj (tmap k) hk
    exact ⟨updS_sh_other _ ω hout tout _ hj', updS_st_other _ ω hout tout _ hj'⟩
  · rw [updS_val]

/-- **Renaming a word program with machine calls.** -/
theorem WXExec.liftX (cap : ℕ) (fs : Fin (ns + 1) → Fin (ns' + 1)) (hfs : Function.Injective fs)
    (fr : Fin nr → Fin nr') (hfr : Function.Injective fr) {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ}
    (h : WXExec cap P σ τ n) :
    ∀ ω : WState ns' nr', LiftW fs fr ω σ →
      ∃ ω', WXExec cap (WMX.liftX fs fr P) ω ω' n ∧ LiftW fs fr ω' τ ∧ OutsideW fs fr ω ω' := by
  induction h with
  | wm h =>
    intro ω hω
    obtain ⟨ω', e, l, o⟩ := WExec.liftW _ cap le_rfl fs hfs fr hfr h ω hω
    exact ⟨ω', WXExec.wm e, l, o⟩
  | @mach t s n M tmap σ hout tout hinj hstep =>
    intro ω hω
    have hstep' : Step M n (fun j => ω.sh ((fs ∘ tmap) j)) (fun j => ω.st ((fs ∘ tmap) j)) hout tout := by
      have e1 : (fun j => ω.sh ((fs ∘ tmap) j)) = fun j => σ.sh (tmap j) := funext fun j => hω.sh (tmap j)
      have e2 : (fun j => ω.st ((fs ∘ tmap) j)) = fun j => σ.st (tmap j) := funext fun j => hω.st (tmap j)
      rw [e1, e2]; exact hstep
    obtain ⟨l, o⟩ := liftW_updS fs hfs fr tmap hinj hω hout tout
    exact ⟨_, WXExec.mach ω (hfs.comp hinj) hstep', l, o⟩
  | seq _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, l2, o2⟩ := ih2 ω1 l1
    exact ⟨ω2, WXExec.seq e1 e2, l2, o1.trans o2⟩
  | ifrT hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih ω hω
    exact ⟨ω1, WXExec.ifrT (by rw [hω.val]; exact hv) e1, l1, o1⟩
  | ifrF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih ω hω
    exact ⟨ω1, WXExec.ifrF (by rw [hω.val]; exact hv) e1, l1, o1⟩
  | ifsT hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih ω hω
    exact ⟨ω1, WXExec.ifsT (by rw [wbit_liftW hω]; exact hv) e1, l1, o1⟩
  | ifsF hv _ ih =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih ω hω
    exact ⟨ω1, WXExec.ifsF (by rw [wbit_liftW hω]; exact hv) e1, l1, o1⟩
  | whrF hv =>
    intro ω hω
    exact ⟨ω, WXExec.whrF (by rw [hω.val]; exact hv), hω, OutsideW.refl fs fr ω⟩
  | whrT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, l2, o2⟩ := ih2 ω1 l1
    exact ⟨ω2, WXExec.whrT (by rw [hω.val]; exact hv) e1 e2, l2, o1.trans o2⟩
  | whsF hv =>
    intro ω hω
    exact ⟨ω, WXExec.whsF (by rw [wbit_liftW hω]; exact hv), hω, OutsideW.refl fs fr ω⟩
  | whsT hv _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih1 ω hω
    obtain ⟨ω2, e2, l2, o2⟩ := ih2 ω1 l1
    exact ⟨ω2, WXExec.whsT (by rw [wbit_liftW hω]; exact hv) e1 e2, l2, o1.trans o2⟩
  | mono _ hle ih =>
    intro ω hω
    obtain ⟨ω1, e1, l1, o1⟩ := ih ω hω
    exact ⟨ω1, WXExec.mono e1 hle, l1, o1⟩

end NearQuarticWires.StageTupleOuter
