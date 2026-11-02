import Proof.Quartic.StageNativeKids.Request
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print` and `prop:time`, paper/paper.tex: all five nonempty original-source fields and six
literal empty fields are acquired by the actual eleven-field loader. -/
def NativeKidsRequest.sourceLoadCost (r : NativeKidsRequest) : ℕ :=
  Top.loadCost (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)

/-- `prop:time`, paper/paper.tex: the actual
finite source and every loader transition determine its paid blank
workspace; no row, pool or computed count is installed in advance. -/
def NativeKidsRequest.sourceLoadCapacity (r : NativeKidsRequest) : ℕ :=
  2 * r.word.length + 1 + Top.loadChainCost
    (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)

/-- `lem:print`, paper/paper.tex: the retained
original call, affine header, binary context, atom and output width
occupy their exact separate source tapes after actual loading. -/
def NativeKidsRequest.loadedSource (r : NativeKidsRequest) : Fin 13 → List Bool :=
  ![frame r.word, r.word, r.sourceFields 0, r.sourceFields 1, r.sourceFields 2,
    r.sourceFields 3, r.sourceFields 4, r.sourceFields 5, r.sourceFields 6,
    r.sourceFields 7, r.sourceFields 8, r.sourceFields 9, r.sourceFields 10]

/-- `lem:print` and `prop:time`, paper/paper.tex: cold original-source extraction executes the actual
eleven-field loader on a disjoint physical bank, with every input bit
and marker charged and no decoded gate or child-pool premise. -/
theorem sourceLoad_run {ns nr : ℕ} (cap : ℕ) (r : NativeKidsRequest)
    (bank : Fin 14 → Fin (ns + 1)) (hb : Function.Injective bank)
    (σ : WState ns nr)
    (hin : (fun j : Fin 14 => σ.st (bank j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.sourceLoadCapacity false))
    (hh : ∀ j, σ.sh (bank j) = 0) :
    ∃ τ, WXExec cap (.mach Top.loadM bank) σ τ r.sourceLoadCost ∧
      (∀ j : Fin 13, τ.st (bank (Fin.castAdd 1 j)) = r.loadedSource j) ∧
      (∀ j : Fin 14, τ.sh (bank j) = 0) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have ld := Top.load_run (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) (r.sourceFields 5) (r.sourceFields 6)
    (r.sourceFields 7) (r.sourceFields 8) (r.sourceFields 9) (r.sourceFields 10)
    r.sourceLoadCapacity
    (by unfold NativeKidsRequest.sourceLoadCapacity NativeKidsRequest.word; omega)
    (by unfold NativeKidsRequest.sourceLoadCapacity; omega)
  obtain ⟨actual, hr, hhead, htape, _⟩ := ld
  change run Top.loadM r.sourceLoadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.sourceLoadCapacity false)) = some actual at hr
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
