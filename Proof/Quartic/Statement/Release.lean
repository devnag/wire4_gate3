import Proof.Quartic.Statement.Joint

/-!
# The release statement: the joint theorem from the published results

`ReleaseStatement` is the type of the release theorem. Its hypothesis is `NearCubicGates.Close.PublishedInputs`,
the structure of the trusted file `Statement.lean` whose six fields transcribe published results the joint
paper assumes: Williams' rectangular multiplication (Corollary 4.4), the verifier of
Ben-Sasson–Chiesa–Genkin–Tromer (Theorem 11.1) at the tuple `(2, 4, 0, 1)`, Shoup's irreducible-polynomial
algorithm (their Algorithm 17), Sudan–Trevisan–Vadhan's list decoding (Theorem 29), and Chen–Williams' proximity
(Lemma 22, at soundness `1/2`) and linear code (Lemma 26). No prime-number-theorem input is assumed. Its
conclusion is
`JointStatement4` (`Joint.lean`): for one rational `γ` and, for every `0 < d < γ/5`, one `K_d`, one `F_d ∈ E^NP`
and one `n₀`,

* `thm:main` (the near-quartic wire lower bound, joint paper `paper/paper.tex`): every
  `SYM∘THR` circuit `C` on `n ≥ n₀` inputs with `W(C) ≤ ⌊n^4/(K_d λ_n^{17/4} μ_n^{15/2})⌋` has
  `agr(C, F_d) < 1 − d`;
* `thm:gates` (the near-cubic gate lower bound): the same conclusion for at most
  `⌊n^3/(2K_d λ_n^{17/4} μ_n^{15/2})⌋` gates, and for charged top weight `Σ_i |c_i|` at most that cap.

No proof is in this file.
-/

set_option autoImplicit false

namespace NearQuarticWires.Release

/-- **The release theorem's type** (`thm:main` and `thm:gates`, joint paper `paper/paper.tex`): the
published results of `NearCubicGates.Close.PublishedInputs` imply `JointStatement4`. -/
def ReleaseStatement : Prop := NearCubicGates.Close.PublishedInputs → NearQuarticWires.Statement.JointStatement4

end NearQuarticWires.Release
