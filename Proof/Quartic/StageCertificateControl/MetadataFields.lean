import Proof.Quartic.StageCertificateControl.RawFields

/-!
# The actual five-field metadata stream at a selected test index

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertTests (TestMetadata)

/-- `sec:algorithm`, paper/paper.tex: metadata uses
exactly its original tag, circuit, sign, digit and threshold codecs. -/
def metadataFields (m : TestMetadata) : List ℕ :=
  [m.tag,m.circuit,m.signOrdinal,m.digitOrdinal,m.threshold]

/-- `sec:algorithm`, paper/paper.tex: each whole-test
record has exactly five fields, independently of its threshold value. -/
theorem metadataFields_length (m : TestMetadata) : (metadataFields m).length=5 := rfl

/-- `sec:algorithm`, paper/paper.tex: concatenating
the actual binary field codecs is the original scheduler word. -/
theorem metadataFields_word (m : TestMetadata) : rawFieldsWord (metadataFields m)=m.word := by
  simp [rawFieldsWord,metadataFields,TestMetadata.word]

/-- `sec:algorithm`, paper/paper.tex: raw field words
concatenate without changing any binary field or delimiter. -/
theorem rawFieldsWord_append (xs ys : List ℕ) :
    rawFieldsWord (xs++ys)=rawFieldsWord xs++rawFieldsWord ys := by simp [rawFieldsWord]

/-- `sec:algorithm`, paper/paper.tex: a complete
metadata list retains every original whole-test field in schedule order. -/
def metadataScalarFields (ms : List TestMetadata) : List ℕ := ms.flatMap metadataFields

/-- `sec:algorithm`, paper/paper.tex: the field
census is exactly five times the actual number of scheduled tests. -/
theorem metadataScalarFields_length (ms : List TestMetadata) :
    (metadataScalarFields ms).length=5*ms.length := by
  induction ms with
  | nil => simp [metadataScalarFields]
  | cons m ms ih =>
    simp only [metadataScalarFields,List.flatMap_cons,List.length_append,metadataFields_length,List.length_cons] at *
    omega

/-- `sec:algorithm`, paper/paper.tex: the literal
raw scheduler output is exactly the complete actual binary-field word. -/
theorem metadataScalarFields_word (ms : List TestMetadata) :
    rawFieldsWord (metadataScalarFields ms)=ms.flatMap TestMetadata.word := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    change rawFieldsWord (metadataFields m++metadataScalarFields ms)=_
    rw [rawFieldsWord_append,metadataFields_word,ih]
    rfl

/-- `sec:algorithm`, paper/paper.tex: the selected
test index determines the actual skipped field count, with no threshold
numeric value used in the loop bound. -/
theorem metadataPrefix_fields_length (ms : List TestMetadata) (j : Fin ms.length) :
    (metadataScalarFields (ms.take j.val)).length=5*j.val := by
  rw [metadataScalarFields_length,List.length_take,Nat.min_eq_left j.isLt.le]

/-- `sec:algorithm`, paper/paper.tex: the literal
scheduler stream decomposes into its actual skipped fields, selected
five fields, and remaining schedule, in the physically traversed order. -/
theorem metadataSelected_word (ms : List TestMetadata) (j : Fin ms.length) :
    ms.flatMap TestMetadata.word=
      rawFieldsWord (metadataScalarFields (ms.take j.val))++
      rawFieldsWord (metadataFields ms[j.val])++
      rawFieldsWord (metadataScalarFields (ms.drop (j.val+1))) := by
  have hs : ms=ms.take j.val++ms[j.val]::ms.drop (j.val+1) := by
    calc
      ms=ms.take j.val++ms.drop j.val := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons j.isLt]
  rw [metadataFields_word,metadataScalarFields_word,metadataScalarFields_word]
  simpa only [List.flatMap_append,List.flatMap_cons,List.append_assoc] using
    congrArg (fun xs => xs.flatMap TestMetadata.word) hs

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the threshold is the fifth binary field, copied after the four original
classification fields rather than expanded as a unary natural value. -/
theorem metadataThreshold_word (m : TestMetadata) :
    m.word=rawFieldsWord ((metadataFields m).take 4)++RepairRepresentation.natWord m.threshold := by
  simp [TestMetadata.word,metadataFields,rawFieldsWord]

end NearQuarticWires.StageCertificateControl
