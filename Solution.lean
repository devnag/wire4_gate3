import Proof.Quartic.Release.Main

/-! # The proof that comparator checks

The statement of `Challenge.lean`, proved by the release theorem `NearQuarticWires.Release.main_from_published`
(`Proof/Quartic/Release/Main.lean`). -/

theorem NearQuarticWires.Release.main_theorem : NearQuarticWires.Release.ReleaseStatement :=
  NearQuarticWires.Release.main_from_published
