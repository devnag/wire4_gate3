import Proof.Quartic.StageLift.StreamSigned

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: retain only the
actual reduced value of an arbitrary original digit or residue field. -/
def readIndexInteger (markers target : Fin MM) : St VV MM :=
  .seq (readSignedMod markers) (.op (.wrM target leftVar))

/-- `lem:print`, paper/paper.tex: one original
integer field is read once, reduced by actual bounded arithmetic, and
written as one bounded index record. No raw magnitude is retained or
supplied to any later per-walk Formula request. -/
theorem readIndexInteger_spec (C : Ctx) (markers target : Fin MM) (hne : target ≠ markers)
    (z : ℤ) (rest : List Bool) (a : DS VV MM) (hc : Cst a) (q : ℕ) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hfit : 2 * q ≤ 2 ^ C.Wd) (hW : 3 ≤ C.Wd)
    (hin : C.inp.drop a.ip = NearCubicGates.Close.Interfaces.intWord z ++ rest)
    (hcursor : a.rc target = (a.ram target).length) :
    Hs C (readIndexInteger markers target) a
      (a.rc markers + 30 * natBitLength z.natAbs + 122) (fun b =>
      b.ram target = a.ram target ++ [(z % (q : ℤ)).toNat] ∧
      b.rc target = a.rc target + 1 ∧
      b.ram markers = wr (a.ram markers) 0 (List.replicate (natBitLength z.natAbs) 1 ++ [0]) ∧
      b.rc markers = natBitLength z.natAbs + 1 ∧
      b.ip = a.ip + (NearCubicGates.Close.Interfaces.intWord z).length ∧
      (∀ other, other ≠ markers → other ≠ target →
        b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b signedStreamScratch) := by
  unfold readIndexInteger
  refine Hs.seq (t2 := 1) (readSignedMod_spec C markers z rest a hc q hq haq hfit hW hin)
    fun b ⟨hbv, _hbq, hbi, hbm, hbmc, hbo, hbsh, hbc, hbf⟩ => ?_
  have hbr : b.ram target = a.ram target := (hbo target hne).1
  have hbrc : b.rc target = a.rc target := (hbo target hne).2
  have hbn : b.env leftVar = (z % (q : ℤ)).toNat := by
    simpa using congrArg Int.toNat hbv
  have hbcur : b.rc target = (b.ram target).length := by rw [hbrc, hbr]; exact hcursor
  refine (hs_wrM C target leftVar b hbcur.le).mono le_rfl ?_
  rintro d rfl
  refine ⟨?_, ?_, ?_, ?_, hbi, ?_, hbsh, ⟨hbc.z, hbc.one, hbc.two⟩, hbf⟩
  · simp only [DS.put, Function.update_self]
    rw [putAt, if_neg (by omega), hbn, hbr]
  · simp only [DS.put, Function.update_self, hbrc]
  · simpa only [DS.put, Function.update_of_ne (Ne.symm hne)] using hbm
  · simpa only [DS.put, Function.update_of_ne (Ne.symm hne)] using hbmc
  · intro other hm ht
    simpa only [DS.put, Function.update_of_ne ht] using hbo other hm

end NearQuarticWires.StageLift
