import Proof.Quartic.StageCertificateControl.BitmapRequest

/-!
# The cold signed-table bitmap word function

Paper: `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the native
bitmap budget includes the actual empty-callee language compiler,
the complete literal input, and every signed source-fold instruction. -/
noncomputable def BitmapRequest.budget {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) : ℕ :=
  langBudget StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) VV MM r.word r.sourceSteps

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: one fixed cold program reads the actual
preparation and complete signed native tables, builds both flag arrays,
tests every padded column, and emits only the final original-center
prefix. Arithmetic widths come from the original arity header. -/
noncomputable def bitmapWordFunction (B1 B2 coefficient degree : ℕ) :
    WordFunction (BitmapRequest B1 B2 coefficient degree) BitmapRequest.word
      BitmapRequest.output BitmapRequest.budget :=
  wordFunction_of_lang BitmapRequest.word BitmapRequest.output StageRecovery.packetCallee
    (bitmapSizes B1 B2 coefficient degree) bitmapProgram BitmapRequest.sourceSteps
    (by
      intro r
      let C := ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) r.word
      cases hd : Program.dispatch B1 B2 r.call with
      | none =>
        obtain ⟨rest,hi⟩ := r.word_default hd
        have htwo := bitmap_context_width B1 B2 coefficient degree r.word
        have hroom : 2<2^C.Wd := by
          have hp := Nat.lt_two_pow_self (n := C.Wd)
          change 2≤C.Wd at htwo
          omega
        obtain ⟨b,n,he,hn,ho⟩ := bitmapProgram_default C rest hi hroom
        exact ⟨b,n,he,by simpa only [BitmapRequest.output,hd] using ho,
          by simpa only [BitmapRequest.sourceSteps,hd] using hn⟩
      | some p =>
        let suffix := Program.parametersWord p.1++frame (Program.witnessPrefix r.call p.1 r.witness)++
          RepairRepresentation.natWord r.tests.length++nativeTestStream r.tests
        have hword : r.word=true::(callWord r.call++suffix) := by
          simpa only [suffix,List.append_assoc] using r.word_selected p hd
        have hw : (callWord r.call).length+2≤C.Wd ∧
            64*(StageCertTests.scheduleHint p.1+1)≤C.Wd := by
          have h := bitmap_context_public hd coefficient degree suffix
          rw [← hword] at h
          exact h
        have hreserve : coefficient*(r.call.n+1)^degree+r.call.n+4≤C.Wd := by
          have h := bitmap_context_reserve B1 B2 coefficient degree r.call suffix
          rw [← hword] at h
          exact h
        have bounds := StageCertTests.scheduleBounds_of_width C p.1 hw.2
        have hT := metadata_count_binary_bounds C p.1 r.call.kind hw.2
        rw [← r.count_selected p hd] at hT
        have hs := Cells.prepare_spec _ p.1 p.2
        have hkn : p.1.k≤r.call.n := (Cells.ParameterRules.k_lt_n hs).le
        have hwidth (test : NativeTest) (ht : test∈r.tests) : test.width+2≤C.Wd := by
          have h := r.widths test ht
          omega
        have hwidthWord (test : NativeTest) (ht : test∈r.tests) : natBitLength test.width+2≤C.Wd := by
          have h := r.widths test ht
          have hb := Control.natBitLength_le_self_succ test.width
          omega
        have hboundWord (test : NativeTest) (ht : test∈r.tests) : natBitLength test.bound+2≤C.Wd := by
          have h := r.threshold_bits p hd test ht
          have hh := hw.2
          omega
        have hin : C.inp=true::(callWord r.call++Program.parametersWord p.1++
            frame (Program.witnessPrefix r.call p.1 r.witness)++
            RepairRepresentation.natWord r.tests.length++nativeTestStream r.tests++[]) := by
          change r.word=_
          simpa only [List.append_nil] using r.word_selected p hd
        obtain ⟨b,n,he,hn,ho⟩ := bitmapProgram_selected C r.call p.1
          (StageCertTests.scheduleHint p.1) (Program.witnessPrefix r.call p.1 r.witness)
          r.tests [] hin hw.1 bounds.parserBits (by have h := hw.2;omega) bounds.parserCounts hkn
          (by omega) (r.lengths p hd) hT.1 hT.2 r.values_fit hwidth hboundWord hwidthWord
        exact ⟨b,n,he,by simpa only [BitmapRequest.output,hd] using ho,
          by simpa only [BitmapRequest.sourceSteps,hd] using hn⟩)
    (by
      intro r
      have h := bitmap_context_width B1 B2 coefficient degree r.word
      change 1≤(ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) r.word).Wd
      omega)

end NearQuarticWires.StageCertificateControl
