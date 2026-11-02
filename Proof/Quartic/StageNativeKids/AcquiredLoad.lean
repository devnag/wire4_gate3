import Proof.Quartic.StageNativeKids.AcquiredWord
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms

attribute [local irreducible] NativeKidsRequest.sourceFields NativeKidsRequest.rolePayload

/-- `lem:print`, paper/paper.tex: the
actual acquired record consists of its unchanged five original fields,
the physically computed role payload and five empty fields. -/
def NativeKidsRequest.acquiredFields (r : NativeKidsRequest) : Fin 11 → List Bool :=
  ![r.sourceFields 0, r.sourceFields 1, r.sourceFields 2, r.sourceFields 3,
    r.sourceFields 4, r.rolePayload, [], [], [], [], []]

/-- `lem:print`, paper/paper.tex: the
computed acquired source uses exactly the literal eleven fields read by
the actual original-source loader. -/
theorem acquiredWord_fields (r : NativeKidsRequest) :
    r.acquiredWord = Top.loadRec (r.acquiredFields 0) (r.acquiredFields 1) (r.acquiredFields 2)
      (r.acquiredFields 3) (r.acquiredFields 4) (r.acquiredFields 5) (r.acquiredFields 6)
      (r.acquiredFields 7) (r.acquiredFields 8) (r.acquiredFields 9) (r.acquiredFields 10) := rfl

/-- `prop:time`, paper/paper.tex: the
actual acquired source determines the complete loader clock. -/
def NativeKidsRequest.acquiredLoadCost (r : NativeKidsRequest) : ℕ :=
  Top.loadCost (r.acquiredFields 0) (r.acquiredFields 1) (r.acquiredFields 2)
    (r.acquiredFields 3) (r.acquiredFields 4) (r.acquiredFields 5) (r.acquiredFields 6)
    (r.acquiredFields 7) (r.acquiredFields 8) (r.acquiredFields 9) (r.acquiredFields 10)

/-- `prop:time`, paper/paper.tex: the
acquired-source loader has only its own paid blank reset workspace. -/
def NativeKidsRequest.acquiredLoadCapacity (r : NativeKidsRequest) : ℕ :=
  2 * r.acquiredWord.length + 1 + Top.loadChainCost
    (r.acquiredFields 0) (r.acquiredFields 1) (r.acquiredFields 2)
    (r.acquiredFields 3) (r.acquiredFields 4) (r.acquiredFields 5) (r.acquiredFields 6)
    (r.acquiredFields 7) (r.acquiredFields 8) (r.acquiredFields 9) (r.acquiredFields 10)

/-- `lem:print`, paper/paper.tex: the
retained acquired source exposes only actual original fields and its
computed role bytes, with no selected gate or child-count field. -/
def NativeKidsRequest.acquiredLoaded (r : NativeKidsRequest) : Fin 13 → List Bool :=
  ![frame r.acquiredWord, r.acquiredWord,
    r.acquiredFields 0, r.acquiredFields 1, r.acquiredFields 2, r.acquiredFields 3,
    r.acquiredFields 4, r.acquiredFields 5, r.acquiredFields 6, r.acquiredFields 7,
    r.acquiredFields 8, r.acquiredFields 9, r.acquiredFields 10]

/-- `lem:print` and `prop:time`, paper/paper.tex: the second real source loader consumes
the exact acquired word on an arbitrary disjoint physical bank,
retaining all fields and resetting every head before actual selection. -/
theorem acquiredLoad_run {ns nr : ℕ} (cap : ℕ) (r : NativeKidsRequest)
    (bank : Fin 14 → Fin (ns + 1)) (hb : Function.Injective bank)
    (σ : WState ns nr)
    (hin : (fun j : Fin 14 => σ.st (bank j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.acquiredWord, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.acquiredLoadCapacity false))
    (hh : ∀ j, σ.sh (bank j) = 0) :
    ∃ τ, WXExec cap (.mach Top.loadM bank) σ τ r.acquiredLoadCost ∧
      (∀ j : Fin 13, τ.st (bank (Fin.castAdd 1 j)) = r.acquiredLoaded j) ∧
      (∀ j : Fin 14, τ.sh (bank j) = 0) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have ld := Top.load_run (r.acquiredFields 0) (r.acquiredFields 1) (r.acquiredFields 2)
    (r.acquiredFields 3) (r.acquiredFields 4) (r.acquiredFields 5) (r.acquiredFields 6)
    (r.acquiredFields 7) (r.acquiredFields 8) (r.acquiredFields 9) (r.acquiredFields 10)
    r.acquiredLoadCapacity
    (by
      rw [← acquiredWord_fields r]
      unfold NativeKidsRequest.acquiredLoadCapacity
      omega)
    (by unfold NativeKidsRequest.acquiredLoadCapacity; omega)
  obtain ⟨actual, hr, hhead, htape, _⟩ := ld
  change run Top.loadM r.acquiredLoadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.acquiredWord, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.acquiredLoadCapacity false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨τ, he, dock⟩ := WXExec.mach_run cap hb σ hh hr
  refine ⟨τ, he, ?_, ?_, dock.val, dock.cell⟩
  · intro j
    rw [dock.st, htape]
    dsimp only
    rw [Fin.addCases_left]
    rfl
  · intro j
    rw [dock.sh, hhead]

end NearQuarticWires.StageNativeKids
