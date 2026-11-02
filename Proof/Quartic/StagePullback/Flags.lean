import Proof.Quartic.StagePullback.CoordinateFlip

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
read the two physical bits selecting the left and right star errors. -/
def flagsProgram : St VV MM :=
  .seq (.op (.rdI Flips.leftFlag)) (.op (.rdI Flips.rightFlag))

def flagsState (a : DS VV MM) (left right : Bool) : DS VV MM :=
  { (a.set Flips.leftFlag left.toNat).set Flips.rightFlag right.toNat with ip := a.ip + 2 }

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: two literal input reads decode the corner
selection and advance the source cursor by exactly two bits. -/
theorem flagsProgram_run (C : Ctx) (a : DS VV MM) (left right : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = [left, right] ++ rest) :
    Hs C flagsProgram a 3 (fun b => b = flagsState a left right) := by
  have h0 : a.ip < C.inp.length := lt_of_drop hin 0 (by simp)
  have h1 : a.ip + 1 < C.inp.length := lt_of_drop hin 1 (by simp)
  have hb0 : bitOf C.inp a.ip = left.toNat := by
    simpa using bitOf_drop hin 0 (by simp)
  have hb1 : bitOf C.inp (a.ip + 1) = right.toNat := by
    simpa using bitOf_drop hin 1 (by simp)
  unfold flagsProgram
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdI C Flips.leftFlag a h0) ?_
  rintro b rfl
  refine Hs.mono (hs_rdI C Flips.rightFlag _ h1) le_rfl ?_
  rintro b rfl
  simp only [hb0, hb1]
  rfl

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
corner-bit reading preserves all scalar codes and arithmetic constants. -/
theorem flagsState_frame (a : DS VV MM) (left right : Bool) :
    Fr a (flagsState a left right) [Flips.leftFlag, Flips.rightFlag] := by
  exact (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))

end NearQuarticWires.StagePullback
