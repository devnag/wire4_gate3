import Proof.Quartic.StagePullback.CoordinateFlip
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.SignedCoefficients

open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms

def value : Fin VV := 50
def magnitude : Fin VV := 51
def sign : Fin VV := 52
def positive : Fin VV := 60
def negative : Fin VV := 61

/-- `imp:pullback`, paper/paper.tex: read the original
signed coefficient's magnitude and low sign bit by actual division. -/
def splitProgram : St VV MM := .op (.dm value v2 magnitude sign)

/-- `imp:pullback` and `prop:time`, paper/paper.tex: one physical division decodes the original fixed signed
coefficient, preserving its field and all other retained metadata. -/
theorem splitProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ)
    (hv : a.env value = SInt.encS z) (hwidth : 2 ≤ C.Wd) :
    Hs C splitProgram a 1 (fun b =>
      b.env magnitude = z.natAbs ∧ b.env sign = (if z < 0 then 1 else 0) ∧
      b.sh = a.sh ∧ Fr a b [magnitude, sign]) := by
  have hfour : 4 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (n := 2) (by decide) hwidth
  refine Hs.mono (hs_dm C value v2 magnitude sign a (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hc.two]; decide)
    (by rw [hc.two]; omega)) le_rfl ?_
  rintro b rfl
  exact ⟨by simp only [DS.set_env_ne _ _ (by decide : magnitude ≠ sign), DS.set_env_self,
    hv, hc.two, SInt.encS_div], by simp only [DS.set_env_self, hv, hc.two, SInt.encS_mod],
    rfl, (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))⟩

/-- `imp:pullback`, paper/paper.tex: physically negate
one signed field, retaining the unique zero encoding. -/
def negateProgram : St VV MM :=
  .ite (.eq value vZ) skipS
    (.ite (.eq sign vZ) (.op (.inc value)) (.op (.sub value v1)))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: signed coefficient negation is paid by literal increment
or subtraction, and the zero field remains exactly zero. -/
theorem negateProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ)
    (hv : a.env value = SInt.encS z) (hs : a.env sign = if z < 0 then 1 else 0)
    (hfit : SInt.encS z + 1 < 2 ^ C.Wd) :
    Hs C negateProgram a 3 (fun b =>
      b.env value = SInt.encS (-z) ∧ b.sh = a.sh ∧ Fr a b [value, vJ]) := by
  unfold negateProgram
  by_cases hz : z = 0
  · subst hz
    refine Hs.mono (Hs.iteT (show value ≠ vZ by decide)
      (by simp [Cnd.eval, hv, hc.z]) (skip_spec a)) (by omega) ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide : value ≠ vJ), hv]; rfl,
      rfl, Fr.set a _ (by simp)⟩
  · have hnonzero : SInt.encS z ≠ 0 := by
      intro h
      exact hz (SInt.encS_inj (h.trans SInt.encS_zero.symm))
    refine Hs.iteF (show value ≠ vZ by decide) (by simp [Cnd.eval, hv, hc.z, hnonzero]) ?_
    by_cases hn : z < 0
    · have henc : SInt.encS z - 1 = SInt.encS (-z) := by
        unfold SInt.encS
        rw [Int.natAbs_neg, if_pos hn, if_neg (show ¬ -z < 0 by omega)]
        omega
      refine Hs.mono (Hs.iteF (show sign ≠ vZ by decide)
        (by simp [Cnd.eval, hs, hn, hc.z])
        (hs_sub C value v1 a (by decide) (by rw [hv, hc.one]; omega))) le_rfl ?_
      rintro b rfl
      exact ⟨by simpa only [DS.set_env_self, hv, hc.one] using henc,
        rfl, Fr.set a _ (by simp)⟩
    · have hp : 0 < z := by omega
      have henc : SInt.encS z + 1 = SInt.encS (-z) := by
        unfold SInt.encS
        rw [Int.natAbs_neg, if_neg hn, if_pos (show -z < 0 by omega)]
      refine Hs.mono (Hs.iteT (show sign ≠ vZ by decide)
        (by simp [Cnd.eval, hs, hn, hc.z])
        (hs_inc C value a (by rw [hv]; exact hfit))) le_rfl ?_
      rintro b rfl
      exact ⟨by simpa only [DS.set_env_self, hv] using henc,
        rfl, Fr.set a _ (by simp)⟩

end NearQuarticWires.StagePullback.SignedCoefficients
