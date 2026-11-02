import Proof.Quartic.StageNativeHeader.Output

/-!
# The named registers of the native header printer

Paper: `lem:print`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

/-! ## The registers of the values -/

/-- `n`, `r`, `b`, `s`, `p` as read. -/
def rN : Fin hnr := 0
def rR : Fin hnr := 1
def rB : Fin hnr := 2
def rS : Fin hnr := 3
def rP : Fin hnr := 4
/-- The dense width. -/
def rW : Fin hnr := 19
/-- `(r/2)·s`. -/
def rM : Fin hnr := 21
/-- The row dimension `d`. -/
def rD : Fin hnr := 22
/-- The stride `2·width + 2`. -/
def rT2 : Fin hnr := 23
/-- The signed record width `q`. -/
def rQ : Fin hnr := 24
/-- `U = 2^d`. -/
def rU : Fin hnr := 25
/-- Loop counters and scratch. -/
def rK1 : Fin hnr := 26
def rV : Fin hnr := 28
def rTmp : Fin hnr := 29

end NearQuarticWires.StageNativeHeader
