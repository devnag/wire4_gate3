import Proof.Quartic.StagePullback.RowFields

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: the three actual
source bits select the two star errors and the native half transposition. -/
def rowFlagsProgram : St VV MM :=
  .seq flagsProgram (.op (.rdI NativeRows.transposeFlag))

def rowFlagsState (a : DS VV MM) (left right transpose : Bool) : DS VV MM :=
  { ((a.set Flips.leftFlag left.toNat).set Flips.rightFlag right.toNat).set
    NativeRows.transposeFlag transpose.toNat with ip := a.ip + 3 }

/-- `imp:pullback` and `prop:time`, paper/paper.tex: three literal source-bit reads decode all native row
flags, paying for the exact source cursor advance. -/
theorem rowFlagsProgram_run (C : Ctx) (a : DS VV MM) (left right transpose : Bool)
    (rest : List Bool) (hin : C.inp.drop a.ip = [left, right, transpose] ++ rest) :
    Hs C rowFlagsProgram a 5 (fun b => b = rowFlagsState a left right transpose) := by
  have h2 : a.ip + 2 < C.inp.length := lt_of_drop hin 2 (by simp)
  have hb2 : bitOf C.inp (a.ip + 2) = transpose.toNat := by
    simpa using bitOf_drop hin 2 (by simp)
  unfold rowFlagsProgram
  refine Hs.seq (t1 := 3) (t2 := 1)
    (flagsProgram_run C a left right (transpose :: rest) (by simpa using hin)) ?_
  rintro b he
  subst he
  refine Hs.mono (hs_rdI C NativeRows.transposeFlag _ h2) le_rfl ?_
  rintro b he
  subst he
  simp only [flagsState, hb2]
  rfl

/-- `imp:pullback`, paper/paper.tex: the physical row
flag reader preserves every original scalar field and signed body bit. -/
theorem rowFlagsState_frame (a : DS VV MM) (left right transpose : Bool) :
    Fr a (rowFlagsState a left right transpose) [Flips.leftFlag, Flips.rightFlag, NativeRows.transposeFlag] :=
  (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

end NearQuarticWires.StagePullback
