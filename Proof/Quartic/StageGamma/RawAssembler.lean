import Proof.Quartic.StageGamma.BankLoad
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Expand.PolyTab

variable {t s : ℕ}

/-- `cor:conditional`, paper/paper.tex: the decoded
working source is physical stream one for every raw tape count. -/
theorem raw_one_val : (1 : Fin (t + 2)).val = 1 := by
  change 1 % (t + 2) = 1
  exact Nat.mod_eq_of_lt (by omega)

/-- `cor:conditional`, paper/paper.tex: a raw kernel
tape follows the external source and its physically decoded copy. -/
def rawSlot (i : Fin t) : Fin (t + 2) := ⟨i.val + 2, by omega⟩

/-- `cor:conditional`, paper/paper.tex: raw kernel
tapes are mapped injectively into the fixed surrounding machine. -/
theorem rawSlot_injective : Function.Injective (rawSlot : Fin t → Fin (t + 2)) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [rawSlot] at this
  omega

/-- `cor:conditional`, paper/paper.tex: all actual
raw kernel input words are serialized in tape-index order. -/
def rawRecords (B : Fin t → List Bool) : TapeRecords (t + 1) :=
  List.ofFn fun i => (rawSlot i, B i)

/-- `cor:conditional`, paper/paper.tex: the complete
source of a raw kernel is a finite list of explicitly framed tape words. -/
def rawInput (B : Fin t → List Bool) : List Bool := recordsWord (rawRecords B)

/-- `prop:time`, paper/paper.tex: a bounded list of
finite emitted words has a bounded actual serialized length. -/
theorem flatMap_length_le {α β : Type} (xs : List α) (f : α → List β) (L : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ L) :
    (xs.flatMap f).length ≤ xs.length * L := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-- `prop:time`, paper/paper.tex: framing the actual
finite bank costs precisely a linear factor in its tape-word bound. -/
theorem rawInput_length_le (B : Fin t → List Bool) (L : ℕ)
    (h : ∀ i, (B i).length ≤ L) : (rawInput B).length ≤ t * (2 * L + 1) := by
  have hh := flatMap_length_le (List.finRange t) (fun i => frame (B i)) (2 * L + 1)
    (by intro i _; rw [frame_length]; have := h i; omega)
  simpa only [rawInput, rawRecords, recordsWord, List.ofFn_eq_map,
    List.flatMap_map, Function.comp_def, List.length_finRange] using hh

/-- `prop:time`, paper/paper.tex: the source loader's
capacity is computed from the actual finite bank contents. -/
def rawCapacity (B : Fin t → List Bool) : ℕ :=
  (rawInput B).length + (∑ i, (B i).length) + 10

/-- `cor:conditional`, paper/paper.tex: the enclosing
finite control loads the records and calls the actual raw kernel. -/
noncomputable def rawProgram (M : Machine t s) : WMX (t + 1) 1 :=
  .seq (.wm (unframeRecord 0 1 0))
    (.seq (.wm (loadTapeSlots 1 0 ((List.finRange t).map rawSlot))) (.mach M rawSlot))

/-- `prop:time`, paper/paper.tex: decoding and every
raw-kernel transition are charged in the surrounding execution. -/
def rawCost (B : Fin t → List Bool) (time : ℕ) : ℕ := 46 * (rawInput B).length + 8 + time

/-- `cor:conditional`, paper/paper.tex: the decoder
has one destination for each raw tape and no input-dependent control. -/
theorem rawRecords_slots (B : Fin t → List Bool) :
    (rawRecords B).map Prod.fst = (List.finRange t).map rawSlot := by
  unfold rawRecords
  rw [List.map_ofFn]
  exact List.ofFn_eq_map

/-- `prop:time`, paper/paper.tex: each raw input
word's length is included in the actual total length. -/
theorem rawLength_le_sum (B : Fin t → List Bool) (i : Fin t) :
    (B i).length ≤ ∑ j, (B j).length :=
  Finset.single_le_sum (fun j _ => Nat.zero_le (B j).length) (Finset.mem_univ i)

/-- `cor:conditional`, paper/paper.tex: an actual
raw execution lifts to a cold enclosing execution, loading all source
words by transitions and preserving every exact output port. -/
theorem raw_run (M : Machine t s) (B A : Fin t → List Bool) (time : ℕ)
    (hkernel : Step M time (fun _ => 0) B (fun _ => 0) A) :
    ∃ τ : WState (t + 1) 1,
      WXExec (rawCapacity B) (rawProgram M) (startState (t + 1) 1 (rawInput B)) τ (rawCost B time) ∧
      (∀ i, τ.st (rawSlot i) = A i) ∧ ∀ i, τ.sh (rawSlot i) = 0 := by
  let σ := startState (t + 1) 1 (rawInput B)
  let σ1 := (σ.sets 1 (rawInput B)).seth 0 (2 * (rawInput B).length + 1)
  have h1 : WExec (rawCapacity B) (unframeRecord 0 1 0) σ σ1
      (23 * (rawInput B).length + 5) := by
    simpa [σ, σ1, startState] using
      unframeRecord_run (rawCapacity B) (0 : Fin (t + 2)) 1 (by simp [Fin.ext_iff]) (0 : Fin 1)
        (rawInput B) [] [] σ (by simp [σ, startState]) rfl rfl rfl
        (by dsimp [rawCapacity]; omega)
  have hn : ((rawRecords B).map Prod.fst).Nodup := by
    rw [rawRecords_slots]
    exact (List.nodup_finRange t).map rawSlot_injective
  have hsafe : ∀ record ∈ rawRecords B, (1 : Fin (t + 2)) ≠ record.1 := by
    intro record hr
    rw [rawRecords] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    intro heq
    have := congrArg Fin.val heq
    change (1 : Fin (t + 2)).val = i.val + 2 at this
    rw [raw_one_val] at this
    omega
  have hcap : ∀ record ∈ rawRecords B, record.2.length ≤ rawCapacity B := by
    intro record hr
    rw [rawRecords] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    have hh := rawLength_le_sum B i
    dsimp only [rawCapacity]
    omega
  have hblank : ∀ record ∈ rawRecords B, σ1.st record.1 = [] ∧ σ1.sh record.1 = 0 := by
    intro record hr
    rw [rawRecords] at hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    have hi : (rawSlot i).val ≠ 0 := by change i.val + 2 ≠ 0; omega
    have hi0 : rawSlot i ≠ (0 : Fin (t + 2)) := fun h => hi (congrArg Fin.val h)
    have hi1 : rawSlot i ≠ (1 : Fin (t + 2)) := by
      intro heq
      have := congrArg Fin.val heq
      change i.val + 2 = (1 : Fin (t + 2)).val at this
      rw [raw_one_val] at this
      omega
    constructor
    · change (Function.update σ.st 1 (rawInput B)) (rawSlot i) = []
      rw [Function.update_of_ne hi1]
      change (if (rawSlot i).val = 0 then frame (rawInput B) else []) = []
      rw [if_neg hi]
    · change (Function.update σ.sh 0 (2 * (rawInput B).length + 1)) (rawSlot i) = 0
      rw [Function.update_of_ne hi0]
      rfl
  have h2 := loadRecords_run (rawCapacity B) (1 : Fin (t + 2)) (0 : Fin 1)
    (rawRecords B) hn hsafe hcap [] [] σ1 (by simp [σ1, rawInput])
    (by change (Function.update σ.sh 0 (2 * (rawInput B).length + 1)) 1 = 0
        rw [Function.update_of_ne (by simp [Fin.ext_iff])]
        rfl)
    (by simp [σ1, σ, startState]) hblank
  let σ2 := loadedRecords 1 σ1 (rawRecords B)
  have h2' : WExec (rawCapacity B)
      (loadTapeSlots 1 0 ((List.finRange t).map rawSlot)) σ1 σ2
      (loadRecordsCost (rawRecords B)) := by
    simpa only [loadRecords_eq_slots, rawRecords_slots] using h2
  have hσ2s : ∀ i, σ2.st (rawSlot i) = B i := by
    intro i
    exact loadedRecords_mem 1 σ1 (rawRecords B) hn (rawSlot i, B i)
      (by rw [rawRecords]; exact List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hσ2h : ∀ i, σ2.sh (rawSlot i) = 0 := by
    intro i
    have hi1 : rawSlot i ≠ (1 : Fin (t + 2)) := by
      intro heq
      have := congrArg Fin.val heq
      change i.val + 2 = (1 : Fin (t + 2)).val at this
      rw [raw_one_val] at this
      omega
    rw [show σ2.sh (rawSlot i) = σ1.sh (rawSlot i) from
      loadedRecords_head 1 (rawSlot i) hi1 σ1 (rawRecords B)]
    change (Function.update σ.sh 0 (2 * (rawInput B).length + 1)) (rawSlot i) = 0
    rw [Function.update_of_ne (show rawSlot i ≠ 0 from by
      intro heq
      have := congrArg Fin.val heq
      change i.val + 2 = 0 at this
      omega)]
    rfl
  have hk : Step M time (fun i => σ2.sh (rawSlot i)) (fun i => σ2.st (rawSlot i)) (fun _ => 0) A := by
    simpa only [hσ2h, hσ2s] using hkernel
  have h3 := WXExec.mach (cap := rawCapacity B) σ2 rawSlot_injective hk
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm h1) (WXExec.seq (WXExec.wm h2') h3)) ?_, ?_, ?_⟩
  · have hh := loadRecordsCost_le (rawRecords B)
    dsimp only [rawCost, rawInput] at *
    omega
  · exact updS_st_slot rawSlot σ2 (fun _ => 0) A rawSlot_injective
  · exact updS_sh_slot rawSlot σ2 (fun _ => 0) A rawSlot_injective

/-- `cor:conditional`, paper/paper.tex: a proved raw
kernel with an exact output port becomes a genuine cold WordFunction;
the entire serialized source and all transition overhead remain paid. -/
noncomputable def rawWordFunction {Request : Type} (M : Machine t s) (OUT : Fin t)
    (B : Request → Fin t → List Bool) (output : Request → List Bool) (time : Request → ℕ)
    (h : ∀ request, ∃ A, Step M (time request) (fun _ => 0) (B request) (fun _ => 0) A ∧
      A OUT = output request) :
    WordFunction Request (fun request => rawInput (B request)) output
      (fun request => 2 * rawCost (B request) (time request) + 2) :=
  wordFunction_of_ideal (rawProgram M) (rawSlot OUT)
    (by change OUT.val + 2 ≠ 0; omega) (fun request => rawCapacity (B request))
    (fun _ _ => 0) (fun request => rawCost (B request) (time request)) (fun _ => le_rfl) (by
      intro request
      obtain ⟨A, hk, ho⟩ := h request
      obtain ⟨τ, hr, hs, _⟩ := raw_run M (B request) A (time request) hk
      refine ⟨rfl, τ, ?_, (hs OUT).trans ho⟩
      simpa only [idealStart, startState, List.replicate_zero] using hr)

end NearQuarticWires.StageGamma
