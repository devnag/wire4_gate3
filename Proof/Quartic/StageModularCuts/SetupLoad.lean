import Proof.Quartic.StageModularCuts.SetupContract

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.WordPrograms

def loadMap (i : Fin 14) : Fin 16 := i.castAdd 2

/-- `lem:print`, paper/paper.tex: the physical
loader occupies one fixed bank of the modular stream machine. -/
theorem loadMap_injective : Function.Injective loadMap := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 16 => x.val) h

/-- `lem:print`, paper/paper.tex: the cold source
is unframed into its actual binary modulus, weak-cut bytes, and two
unary width fields, without a decoded input or cut-count premise. -/
theorem load_spec (cap : ℕ) (r : Request) :
    WXExec cap (.mach Top.loadM loadMap)
      (idealStart 15 16 r.word (lens r)) (loaded r) (loadCost r) := by
  have ld := Top.load_run (natWord r.modulus) r.stream
    (List.replicate r.fieldWidth true) (List.replicate r.width true)
    [] [] [] [] [] [] [] (loadCapacity r)
    (by unfold loadCapacity StagePrint.Downstream.ModularCutsRequest.word; omega)
    (by unfold loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let a := idealStart 15 16 r.word (lens r)
  have hin : (fun j : Fin 14 => a.st (loadMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate (loadCapacity r) false) := by
    funext j
    fin_cases j <;> simp [a, idealStart, loadMap, lens] <;> rfl
  change run Top.loadM (loadCost r)
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate (loadCapacity r) false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨b, eb, dock⟩ := WXExec.mach_run cap loadMap_injective a (fun _ => rfl) hr
  have hloaded (j : Fin 14) :
      (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        (fields r) (fun _ : Fin 1 => List.replicate (loadCapacity r) false)) j =
      (loaded r).st (loadMap j) := by
    fin_cases j <;> rfl
  have hb : b = loaded r := by
    apply WState.eq
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have he : loadMap j = i := Fin.ext rfl
        rw [← he, dock.sh, hh]
        rfl
      · have hn : ∀ j, loadMap j ≠ i := by
          intro j h
          have hv := congrArg (fun x : Fin 16 => x.val) h
          change j.val = i.val at hv
          have hj := j.isLt
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have he : loadMap j = i := Fin.ext rfl
        rw [← he, dock.st, ht]
        exact hloaded j
      · have hn : ∀ j, loadMap j ≠ i := by
          intro j h
          have hv := congrArg (fun x : Fin 16 => x.val) h
          change j.val = i.val at hv
          have hj := j.isLt
          omega
        rw [(dock.other i hn).1]
        simp [a, idealStart, lens, loaded,
          show ¬i.val < 13 by omega, show i.val ≠ 13 by omega]
        intro he
        have hv := congrArg (fun x : Fin 16 => x.val) he
        change i.val = 0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact eb.cast cap hb le_rfl

end NearQuarticWires.StageModularCuts.Setup
