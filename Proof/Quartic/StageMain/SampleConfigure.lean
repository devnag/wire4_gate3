import Proof.Quartic.StageMain.ParameterGet
import Proof.Quartic.StageMain.ColumnState

/-!
# Loading the sampler dimensions from the retained parameter word

Step 4 of `sec:algorithm`, paper/paper.tex,
uses the selected field degree and sample count. Two paid fixed-index
reads install those exact values while retaining the certificate cursor
and every source record.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift SampleCells

def configureSamples : St VV MM := .seq (readParameter 18 ell) (readParameter 17 sampleLimit)

def configureScratch : List (Fin VV) := [t2, vJ, c0, ell, sampleLimit]

theorem configureSamples_run (C : Ctx) (p : Cells.Parameters)
    (a : DS VV MM) (hc : Cst a) (hstore : a.ram parameterStore = parameterScalars p)
    (hfit : 18 < 2 ^ C.Wd) :
    Hs C configureSamples a (a.rc parameterStore + 291) (fun b =>
      b.env ell = p.ellf ∧ b.env sampleLimit = p.Q ∧ b.rc parameterStore = 18 ∧
      parameterRest b = parameterRest a ∧ Cst b ∧ Fr a b configureScratch) := by
  have h18 : (parameterScalars p).getD 18 0 = p.ellf := by
    simp [parameterScalars, parameterHeadScalars]
  have h17 : (parameterScalars p).getD 17 0 = p.Q := by
    simp [parameterScalars, parameterHeadScalars]
  unfold configureSamples
  refine (Hs.seq (t1 := a.rc parameterStore + 139) (t2 := 151)
    ((readParameter_run C p 18 ell a hc hstore hfit (by decide)).mono (by norm_num) (fun _ h => h))
    ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbE, hbrc, hbrest, hbc, hbfr⟩
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hbrest
  have hh := readParameter_run C p 17 sampleLimit b hbc (by rw [hbram]; exact hstore)
    (by omega) (by decide)
  rw [hbrc] at hh
  refine hh.mono (by norm_num) ?_
  rintro d ⟨hdQ, hdrc, hdrest, hdc, hdfr⟩
  refine ⟨?_, hdQ.trans h17, hdrc, hdrest.trans hbrest, hdc, ?_⟩
  · rw [hdfr ell (by decide), hbE]
    exact h18
  · exact (hbfr.weaken (by
      intro x hx; simp only [configureScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)).trans
        (hdfr.weaken (by
          intro x hx; simp only [configureScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto))

end NearQuarticWires.StageMain.Controller
