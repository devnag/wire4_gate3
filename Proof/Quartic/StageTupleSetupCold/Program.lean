import Proof.Quartic.StageTupleSetupCold.Ready
import Proof.Quartic.StageTuplePreparedOutput.Final

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms

namespace Helpers

/-- `lem:print`, paper/paper.tex: source
acquisition is followed by the two independent binary-codec caches.
Neither pass decodes the sampler or walk-ordinal magnitude. -/
noncomputable def prelude (F : Helpers) : WMX F.ns 8 :=
  .seq (.mach Top.loadM F.loader)
    (.seq (.wm (StageTuple.contextFrameProgram F.contextPair (regs 3 (by decide))))
      (.wm (StageTupleSetup.frameNaturalProgram F.degreePair (regs 3 (by decide)))))

/-- `lem:print`, paper/paper.tex: the
whole cold setup executes the actual source loader, literal small
packet framers, four genuine one-shot ordinary calls and the complete
eleven-field prepared formatter. Each private helper bank is used once. -/
noncomputable def finish (F : Helpers) : WMX F.ns 8 :=
  .seq F.widthStage
    (.seq F.rowStage
      (.seq (F.coefficientStage false)
        (.seq (F.coefficientStage true)
          (.wm (StageTuplePreparedOutput.preparedOutputProgram F.preparedPorts
            (regs 4 (by decide)))))))

/-- `lem:print`, paper/paper.tex: the
complete actual cold program acquires its sources before the four
real small helper calls and the prepared-output formatter. -/
noncomputable def program (F : Helpers) : WMX F.ns 8 :=.seq F.prelude F.finish

end Helpers

end NearQuarticWires.StageTupleSetupCold
