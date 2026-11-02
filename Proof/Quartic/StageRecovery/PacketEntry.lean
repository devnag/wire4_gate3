import Proof.Quartic.StageRecovery.NaturalPrint
import Proof.Gates.Cells.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: one native framed
binary sign/magnitude record is decoded, centered, and printed in the
canonical signed-integer codec. Reduced cut coefficients ensure that
the native value is nonnegative. -/
def packetEntry : St VV MM :=
  .seq rdRec (.seq (.op (.copy magnitudeVar t3))
    (.seq (.op (.half magnitudeVar)) (.seq centerNatural emitCentered)))

/-- `prop:time`, paper/paper.tex: the charged per-entry
cost includes native-record scanning, division, centering and printing. -/
def packetEntryCost (width q value : ℕ) : ℕ :=
  12 * width + 12 + (1 + (1 + (20 +
    (40 * natBitLength (naturalSign q value) +
      40 * natBitLength (naturalMagnitude q value) + 85) + 1) + 1) + 1) + 1

/-- `lem:print`, paper/paper.tex: the exact sequential
packet-to-codec operation preserves the modulus and every unmodified
cursor; no input table entry is supplied as a separate integer word. -/
theorem packetEntry_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (width q value : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = frame (binary width (2 * value)) ++ rest)
    (hvalue : 2 * value < 2 ^ width) (hwidth : width + 2 ≤ C.Wd)
    (hq : 0 < q) (haq : a.env modulusVar = q)
    (hqfit : 2 * q ≤ 2 ^ C.Wd) (hW : 1 < 2 ^ C.Wd)
    (hsfit : natBitLength (naturalSign q value) + 2 < 2 ^ C.Wd)
    (hmfit : natBitLength (naturalMagnitude q value) + 2 < 2 ^ C.Wd) :
    Hs C packetEntry a (packetEntryCost width q value) (fun b =>
      b.out = a.out ++ intWord (Walks.centeredResidue q value) ∧
      b.ip = a.ip + (2 * width + 1) ∧ b.env modulusVar = q ∧ Cst b ∧
      Fr a b [t0, t1, t3, vJ, magnitudeVar, quotientVar, remainderVar, halfVar,
        signVar, t5, t6, t7, t8, t9]) := by
  unfold packetEntry packetEntryCost
  refine Hs.seq (rdRec_spec a hc width (2 * value) rest hin hvalue hwidth)
    fun b ⟨hbv, hbp, hbr, hbf⟩ => ?_
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
  refine Hs.seq (hs_copy C magnitudeVar t3 b (by decide)) fun d hd => ?_
  subst d
  refine Hs.seq (hs_half C magnitudeVar _) fun d hd => ?_
  subst d
  let start := (b.set magnitudeVar (b.env t3)).set magnitudeVar
    ((b.set magnitudeVar (b.env t3)).env magnitudeVar / 2)
  have hsq : start.env modulusVar = q := by
    simp (config := {decide := true}) [start, DS.set, hbq]
  have hsv : start.env magnitudeVar = value := by simp [start, hbv]
  have hsc : Cst start := Cst.of_fr (T := [magnitudeVar]) hbc
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))) (by decide)
  have ec := centerNatural_spec C start (by rw [hsq]; exact hq)
    (by rw [hsq]; exact hqfit) hW
  rw [hsq, hsv] at ec
  refine Hs.seq ec fun d ⟨hdv, hds, hdsh, hdf⟩ => ?_
  have hdc : Cst d := Cst.of_fr hsc hdf (by decide)
  have ep := emitCentered_spec C d hdc q value hq hds hdv (by omega) hsfit hmfit
  refine ep.mono le_rfl ?_
  rintro e ⟨heo, her, hec, hef⟩
  have hdsame := Same.of_sh hdsh
  have hesame : e.ip = d.ip := by
    simp only [Prod.mk.injEq] at her
    exact her.1
  have hdo : d.out = b.out := hdsame.out
  have hdi : d.ip = b.ip := hdsame.ip
  have hao : b.out = a.out := by
    simp only [Prod.mk.injEq] at hbr
    exact hbr.1
  refine ⟨by rw [heo, hdo, hao], by rw [hesame, hdi, hbp], ?_, hec, ?_⟩
  · rw [hef _ (by decide), hdf _ (by decide), hsq]
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide))
          (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))))

end NearQuarticWires.StageRecovery
