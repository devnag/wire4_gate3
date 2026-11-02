import Proof.Quartic.StageRecovery.NaturalPrint
import Proof.Quartic.StageRecovery.MobDriver

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: canonical modular
coefficients use the original signed integer codec with sign zero. -/
theorem nonnegative_intWord (c : ℕ) :
    intWord (c : ℤ) = natWord 0 ++ natWord c := by
  simp only [intWord, not_lt.mpr (Int.natCast_nonneg c), if_false, Int.natAbs_natCast]

/-- `lem:print`, paper/paper.tex: a modular coefficient
is emitted as its actual sign-zero field and bounded magnitude field. -/
def emitCoefficientProgram : St VV MM :=
  .seq (emitVariable vZ) (emitVariable coefficientVar)

/-- `lem:print`, paper/paper.tex: the literal two-field
coefficient printer retains every input, record and call-stream head
and emits the unchanged canonical integer word. -/
theorem emitCoefficientProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (c : ℕ) (hcoeff : a.env coefficientVar = c) (hW : 2 ≤ C.Wd)
    (hzero : natBitLength 0 + 2 < 2 ^ C.Wd)
    (hfit : natBitLength c + 2 < 2 ^ C.Wd) :
    Hs C emitCoefficientProgram a
      (40 * natBitLength 0 + 40 * natBitLength c + 85) (fun b =>
        b.out = a.out ++ intWord (c : ℤ) ∧
        (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
          (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
        Cst b ∧ Fr a b [t3, t5, t6, t7, t8, t9]) := by
  unfold emitCoefficientProgram
  refine (Hs.seq (t2 := 40 * natBitLength c + 42)
    (emitVariable_spec C a hc vZ (by decide) hW (by rw [hc.z]; exact hzero))
    fun b ⟨hbo, hbr, hbc, hbf⟩ => ?_).mono (by rw [hc.z]; omega) (fun _ h => h)
  refine (emitVariable_spec C b hbc coefficientVar (by decide) hW
    (by rw [hbf _ (by decide), hcoeff]; exact hfit)).mono
      (by rw [hbf _ (by decide), hcoeff]) ?_
  rintro d ⟨hdo, hdr, hdc, hdf⟩
  refine ⟨?_, hdr.trans hbr, hdc, Fr.trans hbf hdf⟩
  rw [hdo, hbo, hbf _ (by decide), hcoeff, hc.z, nonnegative_intWord, List.append_assoc]

end NearQuarticWires.StageRecovery
