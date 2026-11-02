import Proof.Quartic.StageGamma.Kernel
import Proof.Quartic.StageGamma.BankLoad
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Expand.PolyTab
open NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-- `cor:conditional`, paper/paper.tex: one original
Gamma request and one of its exact eight-slot expansion choices. -/
abbrev PreparedRequest := (request : Machine.GammaRequest) ×
  Cycle.GammaChoice request.parameters.Q

/-- `cor:conditional`, paper/paper.tex: the 31
Gaussian tapes follow the external source and its decoded working copy. -/
def kernelSlot (i : Fin 31) : Fin 33 := ⟨i.val + 2, by omega⟩

/-- `cor:conditional`, paper/paper.tex: Gaussian
tape placement is injective. -/
theorem kernelSlot_injective : Function.Injective kernelSlot := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [kernelSlot] using this

/-- `cor:conditional`, paper/paper.tex: all 31
actual kernel-input words are supplied as finite source records. -/
noncomputable def preparedRecords (r : PreparedRequest) : TapeRecords 32 :=
  List.ofFn fun i : Fin 31 => (kernelSlot i, kernelInput r.1 r.2 i)

/-- `cor:conditional`, paper/paper.tex: the Gaussian
subroutine's complete input includes the cached modulus and every ruler. -/
noncomputable def preparedInput (r : PreparedRequest) : List Bool :=
  recordsWord (preparedRecords r)

/-- `prop:time`, paper/paper.tex: a concrete capacity
for decoding the actual serialized input. -/
noncomputable def preparedCapacity (r : PreparedRequest) : ℕ :=
  (preparedInput r).length + (∑ i : Fin 31, (kernelInput r.1 r.2 i).length) + 10

/-- `cor:conditional`, paper/paper.tex: the fixed
decoder/control program performs one genuine Gaussian machine call. -/
noncomputable def preparedProgram : WMX 32 1 :=
  .seq (.wm (unframeRecord 0 1 0))
    (.seq (.wm (loadTapeSlots 1 0 ((List.finRange 31).map kernelSlot)))
      (.mach SeedFix.elimM kernelSlot))

/-- `prop:time`, paper/paper.tex: the subroutine
includes outer decoding, every record load and the actual kernel cost. -/
noncomputable def preparedCost (r : PreparedRequest) : ℕ :=
  (23 * (preparedInput r).length + 5) + 1 +
    (loadRecordsCost (preparedRecords r) + 1 + Machine.gammaGaussIterationCost r.1 r.2)

/-- `cor:conditional`, paper/paper.tex: source records
have exactly the 31 distinct physical Gaussian destinations. -/
theorem preparedRecords_slots (r : PreparedRequest) :
    (preparedRecords r).map Prod.fst = (List.finRange 31).map kernelSlot := by
  unfold preparedRecords
  rw [List.map_ofFn]
  exact List.ofFn_eq_map

/-- `prop:time`, paper/paper.tex: a single Gaussian
tape's serialized length is included in the total tape length. -/
theorem tapeLength_le_sum (f : Fin 31 → ℕ) (i : Fin 31) : f i ≤ ∑ j, f j :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)

/-- `cor:conditional`, paper/paper.tex: the enclosing
source loader and genuine Gaussian machine execute from the cold start. -/
theorem prepared_run (r : PreparedRequest) :
    ∃ τ : WState 32 1,
      WXExec (preparedCapacity r) preparedProgram
        (startState 32 1 (preparedInput r)) τ (preparedCost r) ∧
      τ.st (kernelSlot 29) = [kernelFlag r.1 r.2] ∧
      τ.st (kernelSlot 30) = List.replicate (kernelExponent r.1 r.2) true ++ [false] ∧
      τ.sh (kernelSlot 29) = 0 ∧ τ.sh (kernelSlot 30) = 0 := by
  let σ := startState 32 1 (preparedInput r)
  let σ1 := (σ.sets 1 (preparedInput r)).seth 0 (2 * (preparedInput r).length + 1)
  have h1 : WExec (preparedCapacity r) (unframeRecord 0 1 0) σ σ1
      (23 * (preparedInput r).length + 5) := by
    simpa [σ, σ1, startState] using
      unframeRecord_run (preparedCapacity r) (0 : Fin 33) 1 (by decide) (0 : Fin 1)
        (preparedInput r) [] [] σ (by simp [σ, startState]) rfl rfl rfl
        (by dsimp [preparedCapacity]; omega)
  have hn : ((preparedRecords r).map Prod.fst).Nodup := by
    rw [preparedRecords_slots]
    exact (List.nodup_finRange 31).map kernelSlot_injective
  have hsafe : ∀ record ∈ preparedRecords r, (1 : Fin 33) ≠ record.1 := by
    intro record hr
    rw [preparedRecords] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    simp only [ne_eq, Fin.ext_iff, kernelSlot]
    omega
  have hcap : ∀ record ∈ preparedRecords r, record.2.length ≤ preparedCapacity r := by
    intro record hr
    rw [preparedRecords] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    have hs : (kernelInput r.1 r.2 i).length ≤ ∑ j : Fin 31, (kernelInput r.1 r.2 j).length :=
      tapeLength_le_sum (fun j => (kernelInput r.1 r.2 j).length) i
    dsimp only [preparedCapacity]
    omega
  have hblank : ∀ record ∈ preparedRecords r, σ1.st record.1 = [] ∧ σ1.sh record.1 = 0 := by
    intro record hr
    rw [preparedRecords] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    have hi : (kernelSlot i).val ≠ 0 := by change i.val + 2 ≠ 0; omega
    have hi1 : kernelSlot i ≠ (1 : Fin 33) := by
      intro heq
      have := congrArg Fin.val heq
      change i.val + 2 = 1 at this
      omega
    have hi0 : kernelSlot i ≠ (0 : Fin 33) := fun heq => hi (congrArg Fin.val heq)
    constructor
    · change (Function.update σ.st 1 (preparedInput r)) (kernelSlot i) = []
      rw [Function.update_of_ne hi1]
      change (if (kernelSlot i).val = 0 then frame (preparedInput r) else []) = []
      rw [if_neg hi]
    · change (Function.update σ.sh 0 (2 * (preparedInput r).length + 1)) (kernelSlot i) = 0
      rw [Function.update_of_ne hi0]
      rfl
  have h2 := loadRecords_run (preparedCapacity r) (1 : Fin 33) (0 : Fin 1)
    (preparedRecords r) hn hsafe hcap [] [] σ1
    (by simp [σ1, preparedInput])
    (by change (Function.update σ.sh 0 (2 * (preparedInput r).length + 1)) 1 = 0
        rw [Function.update_of_ne (by decide)]
        rfl)
    (by simp [σ1, σ, startState]) hblank
  let σ2 := loadedRecords 1 σ1 (preparedRecords r)
  have h2' : WExec (preparedCapacity r)
      (loadTapeSlots 1 0 ((List.finRange 31).map kernelSlot)) σ1 σ2
      (loadRecordsCost (preparedRecords r)) := by
    simpa only [loadRecords_eq_slots, preparedRecords_slots] using h2
  have hσ2s : ∀ i : Fin 31, σ2.st (kernelSlot i) = kernelInput r.1 r.2 i := by
    intro i
    exact loadedRecords_mem 1 σ1 (preparedRecords r) hn (kernelSlot i, kernelInput r.1 r.2 i)
      (by rw [preparedRecords]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hσ2h : ∀ i : Fin 31, σ2.sh (kernelSlot i) = 0 := by
    intro i
    rw [show σ2.sh (kernelSlot i) = σ1.sh (kernelSlot i) from
      loadedRecords_head 1 (kernelSlot i) (by
        intro heq
        have := congrArg Fin.val heq
        change i.val + 2 = 1 at this
        omega) σ1 (preparedRecords r)]
    change (Function.update σ.sh 0 (2 * (preparedInput r).length + 1)) (kernelSlot i) = 0
    rw [Function.update_of_ne (show kernelSlot i ≠ 0 from by
      intro heq
      have := congrArg Fin.val heq
      change i.val + 2 = 0 at this
      omega)]
    rfl
  obtain ⟨tapes, hkernel, hflag, hexponent⟩ := kernel_run_ports r.1 r.2
  have hkernel' : Step SeedFix.elimM (Machine.gammaGaussIterationCost r.1 r.2)
      (fun i => σ2.sh (kernelSlot i)) (fun i => σ2.st (kernelSlot i)) (fun _ => 0) tapes := by
    simpa only [hσ2h, hσ2s] using hkernel
  have h3 := WXExec.mach (cap := preparedCapacity r) σ2 kernelSlot_injective hkernel'
  refine ⟨_, WXExec.seq (WXExec.wm h1) (WXExec.seq (WXExec.wm h2') h3), ?_, ?_, ?_, ?_⟩
  · rw [updS_st_slot kernelSlot σ2 (fun _ => 0) tapes kernelSlot_injective]
    exact hflag
  · rw [updS_st_slot kernelSlot σ2 (fun _ => 0) tapes kernelSlot_injective]
    exact hexponent
  · exact updS_sh_slot kernelSlot σ2 (fun _ => 0) tapes kernelSlot_injective 29
  · exact updS_sh_slot kernelSlot σ2 (fun _ => 0) tapes kernelSlot_injective 30

/-- `prop:time`, paper/paper.tex: the complete prepared
Gaussian call has linear decoding overhead around the genuine kernel. -/
theorem preparedCost_le (r : PreparedRequest) :
    preparedCost r ≤ 46 * (preparedInput r).length + 8 +
      3000 * (Cycle.seedLength r.1.parameters + 9) ^ 6 := by
  have hl := loadRecordsCost_le (preparedRecords r)
  have hk := Machine.gammaGaussIterationCost_le r.1 r.2
  dsimp [preparedCost, preparedInput] at *
  omega

/-- `cor:conditional`, paper/paper.tex: one actual cold
word function returns the conjunction's consistency flag. -/
noncomputable def preparedFlagWordFunction :
    WordFunction PreparedRequest preparedInput (fun r => [kernelFlag r.1 r.2])
      (fun r => 2 * preparedCost r + 2) :=
  wordFunction_of_ideal preparedProgram (kernelSlot 29) (by decide)
    preparedCapacity (fun _ _ => 0) preparedCost (fun _ => le_rfl) (by
      intro r
      obtain ⟨τ, hr, hf, _, _, _⟩ := prepared_run r
      refine ⟨rfl, τ, ?_, hf⟩
      simpa [idealStart, startState] using hr)

/-- `cor:conditional`, paper/paper.tex: one actual cold
word function returns the unary nullity; the flag and nullity together
determine the exact conditional conjunction count. -/
noncomputable def preparedExponentWordFunction :
    WordFunction PreparedRequest preparedInput
      (fun r => List.replicate (kernelExponent r.1 r.2) true ++ [false])
      (fun r => 2 * preparedCost r + 2) :=
  wordFunction_of_ideal preparedProgram (kernelSlot 30) (by decide)
    preparedCapacity (fun _ _ => 0) preparedCost (fun _ => le_rfl) (by
      intro r
      obtain ⟨τ, hr, _, he, _, _⟩ := prepared_run r
      refine ⟨rfl, τ, ?_, he⟩
      simpa [idealStart, startState] using hr)

end NearQuarticWires.StageGamma
