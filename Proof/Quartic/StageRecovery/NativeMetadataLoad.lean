import Proof.Quartic.StageRecovery.NativeDimensions
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the actual outer
record occupies the first fourteen distinct metadata-load streams. -/
def nativeOuterMap (j : Fin 14) : Fin 28 := ⟨j.val, by omega⟩

/-- `lem:print`, paper/paper.tex: native field
extraction reuses only its literal framed source and otherwise has a
fresh bank, preserving both outer header codecs. -/
def nativeInnerMap (j : Fin 14) : Fin 28 :=
  if j.val = 0 then 3 else ⟨j.val + 13, by omega⟩

/-- `lem:print`, paper/paper.tex: distinct native
load streams have no aliases, including the shared actual input. -/
theorem nativeInnerMap_injective : Function.Injective nativeInnerMap := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val h
  simp only [nativeInnerMap] at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> omega

/-- `prop:time`, paper/paper.tex: only the two
actual fixed-loader rulers contain initial blank workspace. -/
def NativeRequest.metadataLens (r : NativeRequest) (i : Fin 28) : ℕ :=
  if i.val = 13 then r.loadCapacity else if i.val = 26 then r.table.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: the exact state
after the physical outer load retains the separate native-load ruler. -/
def NativeRequest.outerLoaded (r : NativeRequest) : WState 27 10 :=
  ⟨fun _ => 0, fun i => if h : i.val < 14 then
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) r.fields
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) ⟨i.val, h⟩
    else if i.val = 26 then List.replicate r.table.loadCapacity false else [],
    fun _ => 0, false⟩

/-- `lem:print`, paper/paper.tex: the cold outer
load has no prepared source tapes; its real framed fields are obtained
by the unchanged fixed native loader. -/
theorem nativeOuterLoad_spec (cap : ℕ) (r : NativeRequest) :
    WXExec cap (.mach Top.loadM nativeOuterMap)
      (idealStart 27 10 r.word r.metadataLens) r.outerLoaded r.loadCost := by
  have ld := Top.load_run (RepairRepresentation.natWord r.modulus) (frame r.table.word)
    (RepairRepresentation.natWord r.targetCount) [] [] [] [] [] [] [] [] r.loadCapacity
    (by unfold NativeRequest.loadCapacity NativeRequest.word; omega)
    (by unfold NativeRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let σ := idealStart 27 10 r.word r.metadataLens
  have hin : (fun j : Fin 14 => σ.st (nativeOuterMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [σ, idealStart, nativeOuterMap, NativeRequest.metadataLens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  have hinj : Function.Injective nativeOuterMap := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 28 => x.val) h)
  obtain ⟨τ, e, dock⟩ := WXExec.mach_run cap hinj σ (fun _ => rfl) hr
  have hτ : τ = r.outerLoaded := by
    apply WState.eq
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : nativeOuterMap j = i := Fin.ext rfl
        rw [← hij, dock.sh, hh]
        rfl
      · have hn : ∀ j, nativeOuterMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [nativeOuterMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : nativeOuterMap j = i := Fin.ext rfl
        rw [← hij, dock.st, ht]
        change (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) _ _ j) =
          r.outerLoaded.st (nativeOuterMap j)
        simp only [NativeRequest.outerLoaded, nativeOuterMap, Fin.val_mk, j.isLt, dif_pos]
        rfl
      · have hn : ∀ j, nativeOuterMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [nativeOuterMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).1]
        have hi0 : i ≠ 0 := by
          intro hz
          have hv := congrArg Fin.val hz
          change i.val = 0 at hv
          omega
        by_cases h26 : i.val = 26 <;>
          simp [σ, idealStart, NativeRequest.metadataLens, NativeRequest.outerLoaded, hi,
            hi0, show i.val ≠ 13 by omega, h26]
    · exact dock.val
    · exact dock.cell
  exact e.cast cap hτ le_rfl

/-- `lem:print`, paper/paper.tex: the second real
field extraction exposes the native width and census and preserves all
outer streams outside its explicit finite bank. -/
theorem nativeInnerLoad_spec (cap : ℕ) (r : NativeRequest) :
    ∃ b, WXExec cap (.mach Top.loadM nativeInnerMap) r.outerLoaded b r.table.loadCost ∧
      Docked nativeInnerMap r.outerLoaded b (fun _ => 0)
        (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) r.table.fields
          (fun _ : Fin 1 => List.replicate r.table.loadCapacity false)) := by
  have ld := Top.load_run (MatrixScoreBatch.physicalInput r.table.matrix)
    (List.replicate r.table.q true) [false] (List.replicate r.table.count true)
    (List.replicate (r.table.q - 1) true) [] [] [] [] [] [] r.table.loadCapacity
    (by unfold StagePrint.TableRequest.loadCapacity StagePrint.TableRequest.word; omega)
    (by unfold StagePrint.TableRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  have hin : (fun j : Fin 14 => r.outerLoaded.st (nativeInnerMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.table.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.table.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [nativeInnerMap, NativeRequest.outerLoaded, NativeRequest.fields] <;> rfl
  change run Top.loadM r.table.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.table.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.table.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨b, hb, hdock⟩ := WXExec.mach_run cap nativeInnerMap_injective r.outerLoaded
    (fun _ => rfl) hr
  refine ⟨b, hb, ?_⟩
  simpa only [hh, ht, StagePrint.TableRequest.fields, StagePrint.TableRequest.word] using hdock

end NearQuarticWires.StageRecovery
