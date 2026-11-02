import Proof.Quartic.StageRecovery.PacketProgram

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: every physical setup,
binary operation, input scan, output write and final head return is
included in the native-packet decoder's actual clock. -/
noncomputable def PacketRequest.budget (r : PacketRequest) : ℕ :=
  langBudget packetCallee packetSizes VV MM r.word r.steps

/-- `lem:print`, paper/paper.tex: an actual cold-input
ordinary word function converts the bounded native table packet into
the complete centered signed-integer list in the same table order. -/
noncomputable def packetWordFunction :
    WordFunction PacketRequest PacketRequest.word PacketRequest.output PacketRequest.budget :=
  wordFunction_of_lang PacketRequest.word PacketRequest.output packetCallee packetSizes
    packetProgram PacketRequest.steps (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := packetProgram_spec
        (ctxOf packetCallee packetSizes r.word) r rfl r.context_width
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := r.context_width
      change 1 ≤ (ctxOf packetCallee packetSizes r.word).Wd
      omega)

end NearQuarticWires.StageRecovery
