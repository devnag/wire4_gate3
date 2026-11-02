import Proof.Quartic.StageCertificateControl.CountProgram
import Proof.Quartic.StageCertTests.PrepScheduleWidth
import Proof.Quartic.Program.Stages

/-!
# A physical test-count word function on every preparation word

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
the default in `sec:params`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- The literal scalar-bootstrap source of `sec:algorithm`,
paper/paper.tex, is exactly the existing preparation word. -/
noncomputable def countWord (B1 B2 : ℕ) (r : Call×List Bool) : List Bool :=
  Program.prepWord B1 B2 r.1 r.2

/-- The whole-test census of `sec:algorithm`, paper/paper.tex, is zero on the default branch and exact on dispatch. -/
noncomputable def countHeaderValue (B1 B2 : ℕ) (c : Call) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 0
  | some p => (StageCertTests.certificateMetadata p.1 c.kind).length

/-- The full charged source clock for the scalar bootstrap,
`prop:time`, paper/paper.tex. -/
noncomputable def countHeaderSteps (B1 B2 : ℕ) (r : Call×List Bool) : ℕ :=
  match Program.dispatch B1 B2 r.1 with
  | none => 50
  | some p => 3*(countCoreCost r.1 p.1 (StageCertTests.scheduleHint p.1)+11)+2

/-- The cold count workspace in `prop:time`, paper/paper.tex, has a fixed positive arithmetic width on every
input, including the literal false-tag default branch. -/
theorem count_context_width (B1 B2 : ℕ) (word : List Bool) :
    2≤(ctxOf StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2) word).Wd := by
  let z := StageCertTests.prepScheduleSizes B1 B2
  have hbase : 2≤z.a1 := by dsimp [z,StageCertTests.prepScheduleSizes];omega
  have hp : 1≤2^(z.c1*leadOnes word) := Nat.one_le_pow _ _ (by decide)
  change 2≤2^(z.c1*leadOnes word)*z.a1
  nlinarith

/-- The actual complete compiled scalar-bootstrap budget,
`prop:time`, paper/paper.tex, includes its true
input word and the fixed empty-callee language compiler. -/
noncomputable def countHeaderBudget (B1 B2 : ℕ) (r : Call×List Bool) : ℕ :=
  langBudget StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2) VV MM
    (countWord B1 B2 r) (countHeaderSteps B1 B2 r)

/-- The actual cold scalar-bootstrap machine of `sec:algorithm`
and `prop:time`, paper/paper.tex,
reads the literal preparation and returns its fully framed exact
whole-test count on every call and witness. No count, decoded record,
bitmap or native table is supplied as a machine input. -/
noncomputable def countWordFunction (B1 B2 : ℕ) :
    WordFunction (Call×List Bool) (countWord B1 B2)
      (fun r => frame (natWord (countHeaderValue B1 B2 r.1))) (countHeaderBudget B1 B2) :=
  wordFunction_of_lang (countWord B1 B2)
    (fun r => frame (natWord (countHeaderValue B1 B2 r.1)))
    StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2) countProgram
    (countHeaderSteps B1 B2)
    (by
      rintro ⟨c,w⟩
      let C := ctxOf StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2)
        (countWord B1 B2 (c,w))
      cases hd : Program.dispatch B1 B2 c with
      | none =>
        have hi : C.inp=false::outputWord (Program.admittedValue B1 B2 Builder.value c w) := by
          dsimp only [C,countWord,Program.prepWord,Program.stageWord]
          rw [hd]
          rfl
        have hr : 2<2^C.Wd := by
          have hw := count_context_width B1 B2 (countWord B1 B2 (c,w))
          change 2≤C.Wd at hw
          have hp := Nat.lt_two_pow_self (n := C.Wd)
          omega
        obtain ⟨b,n,he,hn,ho⟩ := countProgram_default C _ hi hr
        exact ⟨b,n,he,by simpa only [countHeaderValue,hd] using ho,
          by simpa only [countHeaderSteps,hd] using hn⟩
      | some p =>
        have hi : C.inp=true::(callWord c++Program.parametersWord p.1++
            frame (Program.witnessPrefix c p.1 w)) := by
          dsimp only [C,countWord,Program.prepWord,Program.stageWord]
          rw [hd]
          rfl
        have hw0 := StageCertTests.prepSchedule_context_widths hd
          (Program.parametersWord p.1++frame (Program.witnessPrefix c p.1 w))
        have hw : (callWord c).length+2≤C.Wd ∧ 64*(StageCertTests.scheduleHint p.1+1)≤C.Wd := by
          simpa only [C,countWord,Program.prepWord,Program.stageWord,hd,List.append_assoc] using hw0
        obtain ⟨b,n,he,hn,ho⟩ := countProgram_selected C c p.1
          (frame (Program.witnessPrefix c p.1 w)) hi hw.1 hw.2
        exact ⟨b,n,he,by simpa only [countHeaderValue,hd] using ho,
          by simpa only [countHeaderSteps,hd] using hn⟩)
    (by
      intro r
      have h := count_context_width B1 B2 (countWord B1 B2 r)
      change 1≤(ctxOf StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2)
        (countWord B1 B2 r)).Wd
      omega)

end NearQuarticWires.StageCertificateControl
