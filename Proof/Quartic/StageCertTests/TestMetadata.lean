import Proof.Quartic.StageCertTests.ActualPlan
import Proof.Quartic.StageCertTests.PatternParity

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires.RepairRepresentation (natWord)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
one whole-table test is named by its kind, circuit, binary sign
ordinal, digit ordinal and strict natural threshold. -/
structure TestMetadata where
  tag : ℕ
  circuit : ℕ
  signOrdinal : ℕ
  digitOrdinal : ℕ
  threshold : ℕ

/-- `sec:algorithm`, paper/paper.tex:
the moment supplier reads exactly five natural fields after the
unchanged original preparation word. -/
def TestMetadata.word (metadata : TestMetadata) : List Bool :=
  natWord metadata.tag ++ natWord metadata.circuit ++ natWord metadata.signOrdinal ++
    natWord metadata.digitOrdinal ++ natWord metadata.threshold

/-- `sec:algorithm`, paper/paper.tex:
the source request retains its entire preparation prefix literally. -/
def TestMetadata.sourceWord (metadata : TestMetadata) (prep : List Bool) : List Bool :=
  prep ++ metadata.word

/-- `sec:cycle` and `eq:testX`–`eq:testPhi`, paper/paper.tex: typed whole-test ordinals retain the exact
binary sign-pattern ordering used by the physical classifier. -/
inductive TestOrdinal (J : ℕ) where
  | population
  | digit (circuit : Fin 2) (pattern : Fin 256) (position : Fin (J+1))
  | finalError (circuit : Fin 2) (pattern : Fin 256)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the ordinal names its literal mathematical strict-test table. -/
def TestOrdinal.kind {J : ℕ} : TestOrdinal J → TestKind J
  | .population => .population
  | .digit j code r => .digit j (patternOfCode code.val) r
  | .finalError j code => .finalError j (patternOfCode code.val)

/-- `eq:testX`–`eq:testPhi` and `sec:algorithm`, paper/paper.tex: tag zero denotes population, one
denotes a digit test and two denotes final error; irrelevant fields
are the literal zero placeholders. -/
def TestOrdinal.metadata (p : Cells.Parameters) : TestOrdinal (p.J-1) → TestMetadata
  | .population => ⟨0,0,0,0,(p.Xmax+1)^(2*p.k)⟩
  | .digit j code r => ⟨1,j.val,code.val,r.val,p.hE^(8*p.k)⟩
  | .finalError j code => ⟨2,j.val,code.val,0,p.Lambda^(8*p.k)⟩

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
every supplied threshold is the exact selected scalar for its
literal mathematical test table. -/
theorem TestOrdinal.metadata_threshold (p : Cells.Parameters) (test : TestOrdinal (p.J-1)) :
    (test.metadata p).threshold = actualTestThreshold p test.kind := by
  cases test <;> rfl

end NearQuarticWires.StageCertTests
