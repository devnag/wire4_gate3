import Proof.Gates.Cells.Mac

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: each of the seventeen offset branches writes only fixed small literal metadata. -/
def smallLiteral (x : Fin VV) : ℕ→St VV MM
  | 0=>.op (.zero x)
  | n+1=>.seq (smallLiteral x n) (.op (.inc x))

/-- `lem:print` and `prop:time`, paper/paper.tex: a compiled finite offset literal is assigned by actual zero/increment operations. -/
theorem smallLiteral_run (C : Ctx) (x : Fin VV) :
    ∀ (n : ℕ) (a : DS VV MM), n<2^C.Wd→
      Hs C (smallLiteral x n) a (2*n+1) (fun b=>b=a.set x n)
  | 0,a,_=>by simpa only [smallLiteral] using hs_zero C x a
  | n+1,a,h=>by
    unfold smallLiteral
    refine (Hs.seq (t2:=1) (smallLiteral_run C x n a (by omega)) ?_).mono (by omega) (fun _ h=>h)
    rintro b rfl
    refine (hs_inc C x (a.set x n) (by simp;omega)).mono le_rfl ?_
    rintro out rfl
    simp [DS.set,Function.update_idem]

end NearQuarticWires.StagePrint.Header
