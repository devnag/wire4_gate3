import Proof.Quartic.StageColumns.Prepared
import Proof.Quartic.StageColumns.Pair

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm (frameP frame_eq_frameP)
open NearCubicGates.Close.Cells

def columnClock (P : StarParams) : ℕ := PrimT.C4Geo.width P * (bitClock P + 9) + 6

def columnProgram : St VV MM :=
  .seq (forS coordinateIndex nativeWidth emitBitProgram) (.op (.emit false))

/-- `imp:partition`, `lem:print` and `prop:time`, paper/paper.tex: the inner physical loop emits
one exact framed common-generator column directly from its bits. -/
theorem columnProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (j : ℕ)
    (h : Prepared a P) (hj : a.env columnIndex = j) (hjD : j < PrimT.C4Geo.dRow P)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C columnProgram a (columnClock P) (fun b =>
      b.out = a.out ++ frame (PrimT.C4Geo.colBits P j) ∧
      outputRest b = outputRest a ∧ Fr a b columnScratch) := by
  let W := PrimT.C4Geo.width P
  let L := PrimT.C4Geo.colBits P j
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  have hW : W < 2 ^ C.Wd := by have hWn := (dimensions_le P).1; dsimp only [W]; omega
  let I : ℕ → DS VV MM → Prop := fun k b =>
    Prepared b P ∧ b.env columnIndex = j ∧ b.out = a.out ++ frameP (L.take k) ∧
    outputRest b = outputRest a ∧ Fr a b columnScratch
  have hI : ∀ k b value, I k b → I k (b.set coordinateIndex value) := by
    rintro k b value ⟨hp, hbj, hbo, hrest, hf⟩
    have hset : Fr b (b.set coordinateIndex value) columnScratch :=
      Fr.set b _ (List.mem_cons_self ..)
    exact ⟨hp.frame (hset.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)),
      (DS.set_env_ne _ _ (by decide)).trans hbj, hbo, hrest, hf.trans hset⟩
  have h0 : I 0 a := ⟨h, hj, by simp [frameP], rfl, Fr.refl _ _⟩
  unfold columnProgram columnClock
  refine Hs.seq (R1 := fun b => I W b ∧ b.env coordinateIndex = W ∧ b.env nativeWidth = W)
    (t1 := W * (bitClock P + 9) + 4) (t2 := 1) ?_ ?_
  · refine (forS_spec' (C := C) coordinateIndex nativeWidth (by decide)
      emitBitProgram a W hW I (bitClock P + 5) hI h0 h.width ?_).mono
      (by simp only [Nat.add_assoc]; exact le_rfl) (fun _ hs => hs)
    rintro k hk b ⟨hp, hbj, hbo, hrest, hf⟩ hki hkw
    refine (emitBitProgram_run C b P j k (hp.bitInputs hbj hki) hjD hwidth).mono le_rfl ?_
    rintro d ⟨hdo, hdrest, hdf⟩
    have hstep : Fr b d columnScratch :=
      hdf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)
    have hkL : k < L.length := by simpa [L, PrimT.C4Geo.colBits] using hk
    have hget : L[k] = PrimT.C4Geo.colBit P j k := by simp [L, PrimT.C4Geo.colBits]
    refine ⟨⟨hp.frame (hstep.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy)),
      (hdf _ (by decide)).trans hbj, ?_, hdrest.trans hrest, hf.trans hstep⟩,
      (hdf _ (by decide)).trans hki, (hdf _ (by decide)).trans hkw⟩
    rw [hdo, hbo, List.take_succ_eq_append_getElem hkL, hget]
    simp [frameP, List.flatMap_append, List.append_assoc]
  · rintro b ⟨⟨_, _, hout, hrest, hf⟩, _, _⟩
    refine (hs_emit C false b).mono le_rfl ?_
    rintro c rfl
    refine ⟨?_, hrest, hf⟩
    have hlen : L.length = W := by simp [L, W, PrimT.C4Geo.colBits]
    rw [hout, ← hlen, List.take_length, frame_eq_frameP]
    simp only [List.append_assoc]
    rfl

end NearQuarticWires.StageColumns
