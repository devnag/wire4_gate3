import Proof.Quartic.StageCertificateControl.PreparedFold

/-!
# The complete test fold is linear in the native column census

Paper: the three-term time bound `prop:time`, paper/paper.tex, and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- One exact signed table test in `prop:time`, paper/paper.tex, has source cost linear in its native column census
and in the common binary width. -/
theorem NativeTest.sourceCost_le (test : NativeTest) (count width : ℕ)
    (hlen : test.values.length=count) (hw : test.width≤width)
    (hb : natBitLength test.bound≤width) (hwb : natBitLength test.width≤width) :
    test.sourceCost≤100*(count+1)*(width+1) := by
  have hp := Nat.mul_le_mul_left count (Nat.add_le_add_right (Nat.mul_le_mul_left 12 hw) 38)
  unfold NativeTest.sourceCost
  rw [hlen]
  nlinarith

/-- Literal native records in `lem:print` and `prop:time`,
paper/paper.tex, retain a linear
encoded census, including both scalar headers and the terminal delimiter. -/
theorem NativeTest.word_length_le (test : NativeTest) (count width : ℕ)
    (hlen : test.values.length=count) (hw : test.width≤width)
    (hb : natBitLength test.bound≤width) (hwb : natBitLength test.width≤width) :
    test.word.length≤10*(count+1)*(width+1) := by
  have hp := Nat.mul_le_mul_left count (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hw) 1)
  rw [NativeTest.word_length,hlen,natWord_length,natWord_length]
  nlinarith

/-- The counted test fold of `sec:algorithm` and `prop:time`,
paper/paper.tex, retains only a
polynomial test-count factor in addition to its linear native census. -/
theorem testFoldCost_le (tests : List NativeTest) (count width : ℕ)
    (hlen : ∀ test∈tests,test.values.length=count)
    (hw : ∀ test∈tests,test.width≤width)
    (hb : ∀ test∈tests,natBitLength test.bound≤width)
    (hwb : ∀ test∈tests,natBitLength test.width≤width) :
    testFoldCost tests≤(tests.length+1)^2*(100*(count+1)*(width+1)+11) := by
  let A := 100*(count+1)*(width+1)
  have hsum : (tests.map NativeTest.sourceCost).sum≤tests.length*A := by
    have hcost : ∀ test∈tests,test.sourceCost≤A := by
      intro test ht
      exact NativeTest.sourceCost_le test count width (hlen _ ht) (hw _ ht) (hb _ ht) (hwb _ ht)
    induction tests with
    | nil => simp
    | cons test tests ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have ht := hcost test (by simp)
      have hh := ih (fun t hm => hlen t (by simp [hm])) (fun t hm => hw t (by simp [hm]))
        (fun t hm => hb t (by simp [hm])) (fun t hm => hwb t (by simp [hm]))
        (fun t hm => hcost t (by simp [hm]))
      nlinarith
  change tests.length*((tests.map NativeTest.sourceCost).sum+7)+4≤(tests.length+1)^2*(A+11)
  have hm := Nat.mul_le_mul_left tests.length (Nat.add_le_add_right hsum 7)
  nlinarith [Nat.zero_le (tests.length*A)]

/-- The test-major source stream in `prop:time`, paper/paper.tex, occupies linearly many native-width records per test. -/
theorem nativeTestStream_length_le (tests : List NativeTest) (count width : ℕ)
    (hlen : ∀ test∈tests,test.values.length=count)
    (hw : ∀ test∈tests,test.width≤width)
    (hb : ∀ test∈tests,natBitLength test.bound≤width)
    (hwb : ∀ test∈tests,natBitLength test.width≤width) :
    (nativeTestStream tests).length≤tests.length*(10*(count+1)*(width+1)) := by
  induction tests with
  | nil => simp [nativeTestStream]
  | cons test tests ih =>
    have ht := NativeTest.word_length_le test count width (hlen test (by simp)) (hw test (by simp))
      (hb test (by simp)) (hwb test (by simp))
    have hh := ih (fun t hm => hlen t (by simp [hm])) (fun t hm => hw t (by simp [hm]))
      (fun t hm => hb t (by simp [hm])) (fun t hm => hwb t (by simp [hm]))
    simp only [nativeTestStream,List.flatMap_cons,List.length_append,List.length_cons] at *
    nlinarith

end NearQuarticWires.StageCertificateControl
