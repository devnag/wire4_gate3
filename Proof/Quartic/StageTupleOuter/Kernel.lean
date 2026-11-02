import Proof.Quartic.StageTupleOuter.Cost
import Proof.Gates.CheckedPCPP.WMXSim

/-!
# The kernel of the cold tuple printer: loading, initialization and the counted Terms loop

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`kernelProg M` loads the eleven fields of the prepared word (`Top.loadM`, its workspace on tape 13), initializes
the controller (`kernelInitializeProgram`: width, row count and the Terms count, the first empty tuple), and runs the
fixed monomial program of `M` once per monomial in one counted loop on register 17 (`countedSource_run`).
`kernel_run`: from the prepared word on tape 0, the run ends reading like the complete Terms boundary
`progressData r.terms.length`, whose signed cut prefix is the requested output, within the sum of the actual
monomial clocks plus the loader and the initialization.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageTuple

variable {B : StageNativeKids.NativeKidsRequest → ℕ}
  {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
    StageNativeKids.NativeKidsRequest.output B}
  {nativePrice : NativeStagePrice B}

theorem simW_setv' {ns nr : ℕ} {σ σ' : WState ns nr} (hs : SimW σ σ') (r : Fin nr) (v : ℕ) :
    SimW (σ.setv r v) (σ'.setv r v) :=
  ⟨by simp [hs.sh], by simp [hs.val], by simp [hs.cell], fun i => by simpa using hs.st i⟩

/-- The loader's tapes: the thirteen retained source tapes and its workspace on tape 13. -/
def ldBank (span : ℕ) : Fin 14 → Fin (span + 29 + 1) := fun j => ⟨j.val, by omega⟩

theorem ldBank_injective (span : ℕ) : Function.Injective (ldBank span) := fun a b h =>
  Fin.ext (by simpa [ldBank] using congrArg Fin.val h)

/-- **The kernel program.** -/
noncomputable def kernelProg (M : TermStageMachine native nativePrice) : WMX (M.span + 29) 32 :=
  .seq (.mach Top.loadM (ldBank M.span))
    (.seq (.wm (kernelInitializeProgram M.span)) (.whr 17 (.seq (.wm (.dec 17)) M.program)))

/-- The kernel's start: the framed prepared word on tape 0, the loader's blank workspace on tape 13. -/
def kernelStart (span : ℕ) (r : TermCutRequest) : WState (span + 29) 32 :=
  ⟨fun _ => 0, fun i => if i.val = 0 then frame r.preparedWord else
    if i.val = 13 then List.replicate r.preparedLoadCapacity false else [], fun _ => 0, false⟩

/-- The kernel's capacity. -/
def kernelCap (M : TermStageMachine native nativePrice) (r : TermCutRequest) : ℕ :=
  M.capacity r + 4 * (r.stackWidth + 2) + 4 * (r.rowDimension + 2) + 4 * (r.terms.length + 1) + 1

theorem two_pow_nbl_succ_le (x : ℕ) : 2 ^ (natBitLength x + 1) ≤ 4 * x + 4 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hx)
    rw [pow_succ, pow_succ]; omega

/-- **The run of the kernel.** -/
theorem kernel_run (M : TermStageMachine native nativePrice) (r : TermCutRequest) (cap : ℕ)
    (hcap : kernelCap M r ≤ cap) :
    ∃ τ, WXExec cap (kernelProg M) (kernelStart M.span r) τ
        (r.preparedLoadCost + 1 + (kernelInitializeCost r + 1 + countedSourceCost (M.cost r) 0 r.terms.length)) ∧
      SimW ((r.progressData r.terms.length).state M.span r) τ := by
  set span := M.span with hspan
  set ρ0 := kernelStart span r with hρ0
  -- load the eleven fields
  obtain ⟨τ1, e1, l1src, l1h, l1val, l1cell, l1ws, l1o⟩ := preparedLoad_run cap r (ldBank span)
    (ldBank_injective span) ρ0
    (by
      funext j
      fin_cases j <;> rfl)
    (fun _ => rfl)
  -- it reads like the loaded state
  have s1 : SimW (kernelLoadedState span r) τ1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext i
      by_cases hi : i.val < 14
      · have := l1h ⟨i.val, hi⟩
        simpa [ldBank, kernelLoadedState] using this
      · have hb : ∀ j, ldBank span j ≠ i := fun j h => by
          have := congrArg Fin.val h; simp [ldBank] at this; omega
        rw [(l1o i hb).2]; rfl
    · rw [l1val]; rfl
    · rw [l1cell]; rfl
    · intro i
      by_cases hi : i.val < 13
      · have e : ldBank span (Fin.castAdd 1 (⟨i.val, hi⟩ : Fin 13)) = i := Fin.ext (by simp [ldBank])
        have h1 := l1src ⟨i.val, hi⟩
        rw [e] at h1
        simp only [kernelLoadedState, dif_pos hi]
        rw [h1]
        exact RdEq.refl _
      · by_cases h13 : i.val = 13
        · have hi13 : i = ldBank span 13 := Fin.ext (by simp [ldBank, h13])
          rw [hi13, l1ws]
          simp only [kernelLoadedState, ldBank]
          rw [dif_neg (by simp)]
          exact (rdEq_blank _ (by simp)).symm
        · have hb : ∀ j, ldBank span j ≠ i := fun j h => by
            have := congrArg Fin.val h; simp [ldBank] at this; have := j.isLt; omega
          rw [(l1o i hb).1]
          simp only [kernelLoadedState, dif_neg hi, hρ0, kernelStart]
          rw [if_neg (by omega), if_neg h13]
          exact RdEq.refl _
  -- initialize
  have hn := two_pow_nbl_succ_le
  have ei := kernelInitializeProgram_spec cap span r
    (by have := hn (r.stackWidth + 1); unfold kernelCap at hcap; omega)
    (by have := hn (r.rowDimension + 1); unfold kernelCap at hcap; omega)
    (by have := hn r.terms.length; unfold kernelCap at hcap; omega)
    (by unfold kernelCap at hcap; omega)
  obtain ⟨τ2, e2, s2⟩ := wexec_sim ei τ1 s1
  rw [← r.progressData_zero] at s2
  -- the counted Terms loop
  have hloop := countedSource_run (cap := cap) (K := (17 : Fin 32)) (body := M.program) (M.cost r) r.terms.length
    (fun k σ => SimW ((r.progressData k).state span r) σ) (by unfold kernelCap at hcap; omega)
    (by
      intro k hk σ hI hK
      obtain ⟨τ, eτ, sτ⟩ := M.run r k hk cap (by unfold kernelCap at hcap; omega)
      have hsub : r.terms.length - k - 1 = r.terms.length - (k + 1) := by omega
      obtain ⟨τ', eτ', sτ'⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim eτ (σ.setv 17 (r.terms.length - k - 1))
        (by rw [hsub]; exact simW_setv' hI 17 _)
      refine ⟨τ', eτ', NearCubicGates.Close.CheckedPCPP.SimW.trans sτ sτ', ?_⟩
      rw [sτ'.val, sτ.val]
      simp [KernelData.state, TermCutRequest.progressData]
      omega)
    τ2 s2 (by rw [s2.val]; simp [KernelData.state, TermCutRequest.progressData])
  obtain ⟨τ3, e3, s3, _⟩ := hloop
  exact ⟨τ3, WXExec.seq e1 (WXExec.seq (WXExec.wm e2) e3), s3⟩

end NearQuarticWires.StageTupleOuter
