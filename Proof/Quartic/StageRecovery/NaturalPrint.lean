import Proof.Quartic.StageRecovery.NaturalArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:residue`, paper/paper.tex: the natural branch fields
give the exact ordinary signed integer codec, with no negative zero. -/
theorem naturalParts_intWord (q value : ℕ) (hq : 0 < q) :
    intWord (Walks.centeredResidue q value) =
      natWord (naturalSign q value) ++ natWord (naturalMagnitude q value) := by
  rw [← naturalParts_eq q value hq]
  unfold naturalSign naturalMagnitude
  by_cases h : q / 2 < value % q
  · have hm : 0 < q - value % q := Nat.sub_pos_of_lt (Nat.mod_lt _ hq)
    simp [h, NearCubicGates.Close.WordPrograms.SInt.sval, intWord, hm]
  · simp only [h, if_false, show (0 : ℕ) ≠ 1 by decide, decide_false,
      NearCubicGates.Close.WordPrograms.SInt.sval, Bool.false_eq_true]
    simp only [intWord, not_lt.mpr (Int.natCast_nonneg (value % q)), if_false,
      Int.natAbs_natCast]

/-- `lem:print`, paper/paper.tex: copy one binary
variable into the ordinary natural-codec printer. -/
def emitVariable (x : Fin VV) : St VV MM := .seq (.op (.copy t3 x)) emitNatO

/-- `lem:print`, paper/paper.tex: every actual variable
printer writes its complete codec and preserves the remaining input,
stores and call streams. -/
theorem emitVariable_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (x : Fin VV)
    (hx : x ≠ t3) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (emitVariable x) a (40 * natBitLength (a.env x) + 42)
      (fun b => b.out = a.out ++ natWord (a.env x) ∧
        (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
          (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
        Cst b ∧ Fr a b [t3, t5, t6, t7, t8, t9]) := by
  unfold emitVariable
  refine Hs.mono (Hs.seq (t2 := 40 * natBitLength (a.env x) + 40)
    (hs_copy C t3 x a (Ne.symm hx)) (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst b
  have hcb : Cst (a.set t3 (a.env x)) :=
    Cst.of_fr (T := [t3]) hc (Fr.set _ _ (by decide)) (by decide)
  refine (emitNatO_spec _ hcb hW (by simpa only [DS.set_env_self] using hfit)).mono le_rfl ?_
  rintro b ⟨ho, hr, hz, hf⟩
  exact ⟨ho, hr, hz, Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken hf (by decide))⟩

/-- `lem:print`, paper/paper.tex: the centered native
entry is printed as its sign field followed by its magnitude field. -/
def emitCentered : St VV MM := .seq (emitVariable signVar) (emitVariable magnitudeVar)

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1584–1585:
the actual two-field output is precisely the centered integer codec. -/
theorem emitCentered_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q value : ℕ) (hq : 0 < q)
    (hs : a.env signVar = naturalSign q value)
    (hm : a.env magnitudeVar = naturalMagnitude q value)
    (hW : 2 ≤ C.Wd)
    (hsfit : natBitLength (naturalSign q value) + 2 < 2 ^ C.Wd)
    (hmfit : natBitLength (naturalMagnitude q value) + 2 < 2 ^ C.Wd) :
    Hs C emitCentered a
      (40 * natBitLength (naturalSign q value) +
        40 * natBitLength (naturalMagnitude q value) + 85)
      (fun b => b.out = a.out ++ intWord (Walks.centeredResidue q value) ∧
        (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
          (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
        Cst b ∧ Fr a b [t3, t5, t6, t7, t8, t9]) := by
  unfold emitCentered
  have e1 := emitVariable_spec C a hc signVar (by decide) hW (by rw [hs]; exact hsfit)
  rw [hs] at e1
  refine (Hs.seq (t2 := 40 * natBitLength (naturalMagnitude q value) + 42)
    e1 fun b ⟨ho, hr, hz, hf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbm : b.env magnitudeVar = naturalMagnitude q value := by
    rw [hf _ (by decide), hm]
  have e2 := emitVariable_spec C b hz magnitudeVar (by decide) hW
    (by rw [hbm]; exact hmfit)
  rw [hbm] at e2
  refine e2.mono le_rfl ?_
  rintro d ⟨do', dr, dz, df⟩
  refine ⟨?_, dr.trans hr, dz, Fr.trans hf df⟩
  rw [do', ho, naturalParts_intWord q value hq, List.append_assoc]

end NearQuarticWires.StageRecovery
