import Proof.Quartic.StageRecovery.NativeTableFrame
import Bindings.Williams14_Corollary4_4

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery.NativeTableFrame

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the actual complete
signed native table is physically enclosed in one outer frame, including
its terminal record delimiter, for the following packet recovery call. -/
noncomputable def wordFunction (a : WilliamsAlgorithm) :
    WordFunction StagePrint.TableRequest StagePrint.TableRequest.word
      (fun r => frame r.output) (fun r => 2 * steps a r + 2) :=
  wordFunction_of_ideal (program a) (output a)
    (by have ht := (StagePrint.fullTablePrinter a).program.twoTapes
        change 2 ≤ tapes a at ht
        change tapes a ≠ 0
        omega)
    (fun r => 2 * r.output.length + 2) (lens a) (steps a) (fun _ => le_rfl) (by
      intro r
      refine ⟨?_, program_run a r⟩
      unfold lens
      rw [if_neg]
      intro h
      have hh := congrArg Fin.val h
      change tapes a = tapes a + 1 at hh
      omega)

/-- `lem:print`, paper/paper.tex:
the native multiplier is derived from the existing published Williams
Corollary4.4 input through its checked literal binding. -/
noncomputable def publishedAlgorithm
    (h : Bindings.Williams14.Williams14_Corollary4_4) : WilliamsAlgorithm :=
  Classical.choice (Bindings.Williams14.williams14_to_import h)

/-- `lem:print`, paper/paper.tex:
the actual framed native table printer takes only the published source
input; no additional independent multiplication algorithm is assumed. -/
noncomputable def publishedWordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) :
    WordFunction StagePrint.TableRequest StagePrint.TableRequest.word
      (fun r => frame r.output) (fun r => 2 * steps (publishedAlgorithm h) r + 2) :=
  wordFunction (publishedAlgorithm h)

end NearQuarticWires.StageRecovery.NativeTableFrame
