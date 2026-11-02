import Proof.Quartic.StageColumns.Column

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def columnPrefix (P : StarParams) (k : ℕ) : List Bool :=
  (List.range k).flatMap fun j => frame (PrimT.C4Geo.colBits P j)

theorem columnPrefix_succ (P : StarParams) (k : ℕ) :
    columnPrefix P (k + 1) = columnPrefix P k ++ frame (PrimT.C4Geo.colBits P k) := by
  simp [columnPrefix, List.range_succ, List.flatMap_append]

def columnsProgram : St VV MM := forS columnIndex dimension columnProgram

def columnsClock (P : StarParams) : ℕ := PrimT.C4Geo.dRow P * (columnClock P + 4) + 4

/-- `imp:partition`, `lem:print` and `prop:time`, paper/paper.tex: physically enumerate every
canonical basis column in the original order, including all field
markers and zero padding, without a supplied column table. -/
theorem columnsProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (h : Prepared a P) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C columnsProgram a (columnsClock P) (fun b =>
      b.out = a.out ++ columnStream P ∧ outputRest b = outputRest a ∧
      Fr a b generatorScratch) := by
  let N := PrimT.C4Geo.dRow P
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  have hN : N < 2 ^ C.Wd := by have hn := (dimensions_le P).2; dsimp only [N]; omega
  let I : ℕ → DS VV MM → Prop := fun k b =>
    Prepared b P ∧ b.out = a.out ++ columnPrefix P k ∧
    outputRest b = outputRest a ∧ Fr a b generatorScratch
  have hI : ∀ k b value, I k b → I k (b.set columnIndex value) := by
    rintro k b value ⟨hp, hbo, hrest, hf⟩
    have hset : Fr b (b.set columnIndex value) generatorScratch :=
      Fr.set b _ (List.mem_cons_self ..)
    exact ⟨hp.frame hset, hbo, hrest, hf.trans hset⟩
  have h0 : I 0 a := ⟨h, by simp [columnPrefix], rfl, Fr.refl _ _⟩
  unfold columnsProgram columnsClock
  refine (forS_spec' (C := C) columnIndex dimension (by decide) columnProgram a N hN I
    (columnClock P) hI h0 h.dimension ?_).mono le_rfl ?_
  · rintro k hk b ⟨hp, hbo, hrest, hf⟩ hki hkn
    refine (columnProgram_run C b P k hp hki hk hwidth).mono le_rfl ?_
    rintro d ⟨hdo, hdrest, hdf⟩
    have hstep : Fr b d generatorScratch :=
      hdf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)
    refine ⟨⟨hp.frame hstep, ?_, hdrest.trans hrest, hf.trans hstep⟩,
      (hdf _ (by decide)).trans hki, (hdf _ (by decide)).trans hkn⟩
    rw [hdo, hbo, columnPrefix_succ, List.append_assoc]
  · rintro b ⟨⟨_, hbo, hrest, hf⟩, _, _⟩
    exact ⟨hbo, hrest, hf⟩

end NearQuarticWires.StageColumns
