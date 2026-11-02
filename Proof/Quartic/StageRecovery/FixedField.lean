import Proof.Quartic.StageRecovery.FixedBits

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery.FixedBits

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5.GF2

/-- `lem:print`, paper/paper.tex: the fixed-width field
writer visits each bit exactly once before emitting both closing markers. -/
def emitFixedField : St VV MM :=
  .seq (forS index width bitStep) (StageLift.emitLiteral [true, false, false])

/-- `lem:print`, paper/paper.tex: the complete binary
writer modifies only its own word, cursor, quotient and digit registers. -/
def fieldScratch : List (Fin VV) := index :: bitScratch

/-- `lem:print`, paper/paper.tex: the actual four-bit
groups and final three markers equal two full physical framing layers. -/
theorem bitGroups_frame (bits : List Bool) :
    bits.flatMap bitGroup ++ [true, false, false] = frame (frame bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      change [true, true, true, bit] ++ (bits.flatMap bitGroup ++ [true,false,false]) =
        [true,true,true,bit] ++ frame (frame bits)
      rw [ih]

/-- `lem:print`, paper/paper.tex: a finite ordinary
program emits the exact double-framed field in linear bit width. All
input, cache and callee cursors are retained; no bit-value oracle is used. -/
theorem emitFixedField_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (v W : ℕ) (hv : a.env value = v) (hw : a.env width = W)
    (hW : W < 2 ^ C.Wd) (hctx : 2 ≤ C.Wd) :
    Hs C emitFixedField a (18 * W + 12) (fun b =>
      b.out = a.out ++ frame (frame (binary W v)) ∧
      outputRest b = outputRest a ∧ b.env width = W ∧ Cst b ∧ Fr a b fieldScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env value = v / 2 ^ k ∧
    b.out = a.out ++ ((binary W v).take k).flatMap bitGroup ∧
    outputRest b = outputRest a ∧ Cst b ∧ Fr a b fieldScratch
  have hinit : I 0 a := ⟨by simpa using hv, by simp, rfl, hc, Fr.refl _ _⟩
  unfold emitFixedField
  refine (Hs.seq (t2 := 7) (forS_spec' (C := C) index width (by decide) bitStep a W hW I 14
    ?_ hinit hw ?_) fun b ⟨⟨hbv, hbo, hbr, hbc, hbf⟩, hbi, hbw⟩ => ?_).mono (by omega) (fun _ h => h)
  · intro k b val ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by simpa (config := {decide := true}) [DS.set] using h1, h2, h3,
      Cst.of_fr (T := [index]) h4 (Fr.set _ _ (by decide)) (by decide),
      Fr.trans h5 (Fr.set _ _ (by simp [fieldScratch]))⟩
  · intro k hk b ⟨h1, h2, h3, h4, h5⟩ hbi hbw
    refine (bitStep_spec C b h4 (v / 2 ^ k) h1 hctx).mono le_rfl ?_
    rintro d ⟨hd1, hd2, hd3, hd4, hd5⟩
    refine ⟨⟨?_, ?_, hd3.trans h3, hd4,
      Fr.trans h5 (Fr.weaken hd5 (by intro y hy; simp [fieldScratch, hy]))⟩,
      by rw [hd5 _ (by decide), hbi], by rw [hd5 _ (by decide), hbw]⟩
    · rw [hd1, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [hd2, h2, List.take_succ_eq_append_getElem (by simpa only [binary_length] using hk),
        List.flatMap_append, List.flatMap_singleton, List.append_assoc,
        binary_getElem, Nat.testBit_eq_decide_div_mod_eq]
  · refine (StageLift.emitLiteral_spec C [true, false, false] b hbc).mono le_rfl ?_
    rintro d ⟨hdo, hdr, hdc, hdf⟩
    refine ⟨?_, hdr.trans hbr, by rw [hdf _ (by decide), hbw], hdc,
      Fr.trans hbf (Fr.weaken hdf (by decide))⟩
    rw [hdo, hbo, List.take_of_length_le (by rw [binary_length]), List.append_assoc, bitGroups_frame]

end NearQuarticWires.StageRecovery.FixedBits
