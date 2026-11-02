import Proof.Quartic.StageRecovery.FamilyInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand
open NearCubicGates.Close.Expand.PolyTab (idealStart)

/-- `prop:time`, paper/paper.tex: the family loader has
one bounded blank log stream and otherwise starts from its sole input. -/
def FamilyRequest.lens (r : FamilyRequest) (i : Fin 17) : ℕ :=
  if i.val = 13 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: the eleven actual
finite setup fields are physically loaded into the family work bank. -/
theorem familyLoad_spec (cap : ℕ) (r : FamilyRequest) :
    WXExec cap (.mach Top.loadM familyLoadMap)
      (idealStart 16 15 r.word r.lens) r.loaded r.loadCost := by
  have ld := Top.load_run (r.fields 0) (r.fields 1) (r.fields 2) (r.fields 3) (r.fields 4) (r.fields 5)
    (r.fields 6) (r.fields 7) (r.fields 8) (r.fields 9) (r.fields 10) r.loadCapacity
    (by unfold FamilyRequest.loadCapacity FamilyRequest.word; omega)
    (by unfold FamilyRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let σ := idealStart 16 15 r.word r.lens
  have hin : (fun j : Fin 14 => σ.st (familyLoadMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [σ, idealStart, familyLoadMap, FamilyRequest.lens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  have hinj : Function.Injective familyLoadMap := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 17 => x.val) h)
  obtain ⟨τ, e, dock⟩ := WXExec.mach_run cap hinj σ (fun _ => rfl) hr
  have hτ : τ = r.loaded := by
    apply WState.eq
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : familyLoadMap j = i := Fin.ext rfl
        rw [← hij, dock.sh, hh]
        rfl
      · have hn : ∀ j, familyLoadMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [familyLoadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : familyLoadMap j = i := Fin.ext rfl
        rw [← hij, dock.st, ht]
        change (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) _ _ j) =
          r.loaded.st (familyLoadMap j)
        simp only [FamilyRequest.loaded, familyLoadMap, Fin.val_mk, j.isLt, dif_pos]
        rfl
      · have hn : ∀ j, familyLoadMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [familyLoadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).1]
        simp [σ, idealStart, FamilyRequest.lens, FamilyRequest.loaded, hi,
          show i.val ≠ 0 by omega, show i.val ≠ 13 by omega]
        intro hz
        have hv := congrArg Fin.val hz
        change i.val = 0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact e.cast cap hτ le_rfl

end NearQuarticWires.StageRecovery
