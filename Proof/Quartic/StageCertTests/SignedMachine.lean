import Proof.Quartic.StageCertTests.SignedProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery (packetCallee packetSizes)

/-- `prop:time`, paper/paper.tex:
the actual signed converter budget includes cold setup, decoding,
binary arithmetic and all output framing operations. -/
noncomputable def SignedRequest.budget (r : SignedRequest) : ℕ :=
  langBudget packetCallee packetSizes VV MM r.word r.steps

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: an actual cold ordinary word
function converts arbitrary signed native moments to their canonical list. -/
noncomputable def signedWordFunction :
    WordFunction SignedRequest SignedRequest.word SignedRequest.output SignedRequest.budget :=
  wordFunction_of_lang SignedRequest.word SignedRequest.output packetCallee packetSizes
    signedProgram SignedRequest.steps (by
      intro r
      obtain ⟨b,n,he,hn,ho⟩ := signedProgram_spec
        (ctxOf packetCallee packetSizes r.word) r rfl r.context_width
      exact ⟨b,n,he,ho,hn⟩) (by
      intro r
      have h := r.context_width
      change 1 ≤ (ctxOf packetCallee packetSizes r.word).Wd
      omega)

end NearQuarticWires.StageCertTests
