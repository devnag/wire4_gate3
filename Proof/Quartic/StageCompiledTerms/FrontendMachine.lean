import Proof.Quartic.StageCompiledTerms.Frontend

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Expand.PolyTab

/-- Step 3 and `lem:print`, paper/paper.tex: one fixed ordinary machine obtains its entire tagged
batch input by physically streaming the actual raw carrier bytes. -/
noncomputable def carrierFrontendWordFunction :
    WordFunction RawCarrier RawCarrier.word (fun r=>frame r.batchWord)
      (fun r=>2*r.frontSteps+2) :=
  wordFunction_of_ideal (.wm carrierFrontend) (3 : Fin 4) (by decide)
    RawCarrier.frontCapacity (fun _ _=>0) RawCarrier.frontSteps (fun _=>le_rfl) (by
      intro r
      obtain ⟨final,he,hout⟩:=carrierFrontend_spec r
      exact ⟨rfl,final,NearCubicGates.Close.WordPrograms.WXExec.wm he,hout⟩)

end NearQuarticWires.StageCompiledTerms
