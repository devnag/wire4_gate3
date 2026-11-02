import Proof.Quartic.StageNativeHeader.Pre

/-!
# The work before the emission never touches the output

Paper: `lem:print`, paper/paper.tex.

`WM.touches i P` lists whether an instruction of `P` moves or writes the stream `i`; a program that does not touch
`i` avoids it (`avoids_of_touches`). `postP` avoids `sOUT` (`post_avoids`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires.WireExponent3_5.FinalPass.Tm NearQuarticWires.Control

variable {ns nr : ℕ}

/-- Whether an instruction of the program moves or writes the stream `i`. -/
def WM.touches (i : Fin (ns + 1)) : WM ns nr → Bool
  | .skip => false
  | .inc _ => false
  | .dec _ => false
  | .fwd j => decide (j = i)
  | .bwd j => decide (j = i)
  | .wr j _ => decide (j = i)
  | .setc _ => false
  | .seq P Q => WM.touches i P || WM.touches i Q
  | .ifr _ P Q => WM.touches i P || WM.touches i Q
  | .ifs _ P Q => WM.touches i P || WM.touches i Q
  | .whr _ P => WM.touches i P
  | .whs _ P => WM.touches i P

theorem avoids_of_touches (i : Fin (ns + 1)) : ∀ P : WM ns nr, WM.touches i P = false → WM.Avoids i P
  | .skip, _ => trivial
  | .inc _, _ => trivial
  | .dec _, _ => trivial
  | .fwd j, h => by simpa [WM.touches, WM.Avoids] using h
  | .bwd j, h => by simpa [WM.touches, WM.Avoids] using h
  | .wr j _, h => by simpa [WM.touches, WM.Avoids] using h
  | .setc _, _ => trivial
  | .seq P Q, h => by
    simp only [WM.touches, Bool.or_eq_false_iff] at h
    exact ⟨avoids_of_touches i P h.1, avoids_of_touches i Q h.2⟩
  | .ifr _ P Q, h => by
    simp only [WM.touches, Bool.or_eq_false_iff] at h
    exact ⟨avoids_of_touches i P h.1, avoids_of_touches i Q h.2⟩
  | .ifs _ P Q, h => by
    simp only [WM.touches, Bool.or_eq_false_iff] at h
    exact ⟨avoids_of_touches i P h.1, avoids_of_touches i Q h.2⟩
  | .whr _ P, h => avoids_of_touches i P h
  | .whs _ P, h => avoids_of_touches i P h

/-- **The work before the emission avoids the output.** -/
theorem post_avoids : WM.Avoids sOUT postP := avoids_of_touches _ _ (by decide)

/-- **The input part avoids the output.** -/
theorem pre_avoids : WM.Avoids sOUT preP := avoids_of_touches _ _ (by decide)

end NearQuarticWires.StageNativeHeader
