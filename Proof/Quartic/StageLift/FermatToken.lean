import Proof.Quartic.StageLift.TargetToken

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:residue` and `lem:print`, paper/paper.tex: the selected prime supplies the actual exponent token. -/
def emitFermatPower : St VV MM :=
  .seq (.op (.copy targetValue degreePrime))
    (.seq (.op (.sub targetValue v1))
      (emitPrefixedVariable (natWord 6) targetValue))

/-- `lem:residue` and `lem:print`, paper/paper.tex: after the physically emitted form and target subtraction,
the actual exponent and final subtraction complete one Fermat factor. -/
def finishFermatFactor : St VV MM :=
  .seq emitFermatPower (emitOperator .sub)

/-- `lem:residue` and `lem:print`, paper/paper.tex: p−1 is computed and written in the literal postfix
power codec, without being supplied as precomputed formula metadata. -/
theorem emitFermatPower_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (prime : ℕ) (hp : 1 ≤ prime) (hprime : a.env degreePrime = prime)
    (hW : 2 ≤ C.Wd) (hBit : natBitLength prime + 2 < 2 ^ C.Wd) :
    Hs C emitFermatPower a (40 * natBitLength prime + 62) (fun b =>
      b.out = a.out ++ tokWord (.pow (prime - 1)) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (targetValue :: tokenScratch)) := by
  have hbits := codec_nbl_mono (Nat.sub_le prime 1)
  have htag : (natWord 6).length = 7 := by decide
  unfold emitFermatPower
  refine (Hs.seq (t2 := 40 * natBitLength prime + 60)
    (hs_copy C targetValue degreePrime a (by decide)) fun b hb => ?_).mono
      (by omega) (fun _ h => h)
  subst b
  let s1 := a.set targetValue (a.env degreePrime)
  refine (Hs.seq (t2 := 40 * natBitLength prime + 58)
    (hs_sub C targetValue v1 s1 (by decide)
      (by dsimp [s1]; vsimp [hprime, hc.one]; exact hp)) fun b hb => ?_).mono
        (by omega) (fun _ h => h)
  subst b
  let s2 := s1.set targetValue (s1.env targetValue - s1.env v1)
  have hv : s2.env targetValue = prime - 1 := by
    dsimp [s2, s1]
    vsimp [hprime, hc.one]
  have hf : Fr a s2 [targetValue] :=
    (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))
  have hs2 : Cst s2 := Cst.of_fr hc hf (by decide)
  refine (emitPrefixedVariable_spec C (natWord 6) targetValue (by decide) (by decide)
    s2 hs2 hW (by rw [hv]; omega)).mono (by rw [htag, hv]; omega) ?_
  rintro b ⟨hbo, hbrest, hbc, hbf⟩
  refine ⟨?_, hbrest, hbc, (hf.weaken (by simp)).trans (hbf.weaken (by
    intro x hx
    simp only [List.mem_cons]
    tauto))⟩
  rw [hv, show s2.out = a.out from rfl] at hbo
  simpa only [tokWord, List.append_assoc] using hbo

/-- `lem:residue` and `lem:print`, paper/paper.tex: the complete real suffix of each Fermat factor has
the unchanged original power/subtraction tokens and paid binary cost. -/
theorem finishFermatFactor_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (prime : ℕ) (hp : 1 ≤ prime) (hprime : a.env degreePrime = prime)
    (hW : 2 ≤ C.Wd) (hBit : natBitLength prime + 2 < 2 ^ C.Wd) :
    Hs C finishFermatFactor a (40 * natBitLength prime + 78) (fun b =>
      b.out = a.out ++ tokWord (.pow (prime - 1)) ++ tokWord .sub ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (targetValue :: tokenScratch)) := by
  unfold finishFermatFactor
  have hsub : 2 * (tokWord .sub).length + 1 = 15 := by decide
  refine Hs.seq (t2 := 15) (emitFermatPower_spec C a hc prime hp hprime hW hBit)
    fun b ⟨hbo, hbrest, hbc, hbf⟩ => ?_
  have he := emitOperator_spec C .sub b hbc
  rw [hsub] at he
  refine he.mono le_rfl ?_
  rintro d ⟨hdo, hdrest, hdc, hdf⟩
  refine ⟨by rw [hdo, hbo], hdrest.trans hbrest, hdc, hbf.trans ?_⟩
  exact hdf.weaken (by intro x hx; simp only [tokenScratch, List.mem_cons] at hx ⊢; tauto)

end NearQuarticWires.StageLift
