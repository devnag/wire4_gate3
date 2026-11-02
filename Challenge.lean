import Proof.Quartic.Statement.Release

/-! # The statement that comparator checks

The joint theorem of the paper (`paper/paper.tex`, `thm:main` and `thm:gates`, "Almost-everywhere near-quartic
wire lower bound" and "Almost-everywhere near-cubic gate lower bound"), stated from the statement files
(`Statement.lean`, `Proof/Quartic/Statement/Final.lean`, `Joint.lean` and `Release.lean`)
and Mathlib alone: `NearQuarticWires.Release.ReleaseStatement` says that the published results (the fields of
`NearCubicGates.Close.PublishedInputs`, each a published statement transcribed in `Statement.lean`) imply
`NearQuarticWires.Statement.JointStatement4`.

The proof is left open on purpose. `comparator` (`make comparator`; README) checks that `Solution.lean` proves exactly
this statement. `Check.lean` does not import this file, and `make` does not build it. -/

set_option warningAsError false

theorem NearQuarticWires.Release.main_theorem : NearQuarticWires.Release.ReleaseStatement :=
  sorry
