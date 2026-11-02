import Proof.Quartic.StageCert.MomentSourceMachine
import Proof.Quartic.StageMain.CompilerRuntime
import Proof.Quartic.StageMain.RuntimeSource
import Proof.Quartic.StageCertTests.ParameterReadCost

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `prop:time`, paper/paper.tex: the runtime
scale includes the actual source workspace, finite callee reserves,
compiler dimensions and every fixed allocator coefficient/exponent. -/
noncomputable def MomentRequest.runtimeScale {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  let z := momentSourceSizes B1 B2
  let header := 1+natBitLength r.call.n
  r.bodyScale+z.W header+z.Lk header+z.Bk header+
    z.a1+z.c1+z.a2+z.c2+z.a3+z.c3+
    TSK (structuralSourceCallee B1 B2)+VV+MM+r.call.n+1000

/-- `prop:time`, paper/paper.tex: the actual
source scale and all fixed arithmetic constants are included in the
runtime envelope, before any certification predicate is evaluated. -/
theorem MomentRequest.runtimeScale_basic {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    1000≤r.runtimeScale ∧ r.bodyScale≤r.runtimeScale ∧ r.word.length≤r.runtimeScale := by
  have hh : r.word.length≤r.bodyScale := by unfold MomentRequest.bodyScale; omega
  dsimp only [MomentRequest.runtimeScale]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual ordinary compiler clock is linear in
source work and input length, with its displayed quadratic word factor. -/
theorem MomentRequest.compiler_budget_le {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (suffix : List Bool) (steps : ℕ) :
    langBudget (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) VV MM
      (r.word++suffix) steps≤10000*r.runtimeScale^2*(steps+(r.word++suffix).length+1) := by
  let S := r.runtimeScale
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hheader : leadOnes (r.word++suffix)≤S := by
    rw [r.source_header]
    have hh : natBitLength r.call.n≤r.call.n+1 := by
      unfold natBitLength
      have hh := Nat.log_le_self 2 r.call.n
      omega
    dsimp only [S,MomentRequest.runtimeScale]
    omega
  apply Runtime.langBudget_le _ _ _ _ _ _ S hS
  all_goals first
    | exact hheader
    | (rw [r.source_header]; dsimp only [S,MomentRequest.runtimeScale]; omega)
    | (dsimp only [S,MomentRequest.runtimeScale]; omega)

/-- `lem:print` and `prop:time`, paper/paper.tex: cold parameter/call/witness acquisition and all six
actual metadata reads have a cubic runtime-scale source clock. -/
theorem MomentRequest.readSteps_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.readSteps≤110000*r.runtimeScale^3 := by
  let S := r.runtimeScale
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hword : r.word.length≤S := r.runtimeScale_basic.2.2
  have hprep : (compactInput r.call r.selected.1 r.retainedWitness).length≤S := by
    change (compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)).length≤S
    rw [←prepWord_eq_compact r.dispatched r.witness]
    exact r.prep_length_le.trans hword
  have hp : (Program.parametersWord r.selected.1).length≤S :=
    (Runtime.compact_lengths r.call r.selected.1 r.retainedWitness).2.1.trans hprep
  have hr : parameterReadCost r.selected.1 (compactInput r.call r.selected.1 r.retainedWitness).length≤
      20000*S^2 := by
    calc
      _≤5000*((Program.parametersWord r.selected.1).length+1)*
          ((compactInput r.call r.selected.1 r.retainedWitness).length+1) :=
        StageCertTests.parameterReadCost_le_word _ _
      _≤5000*(S+1)*(S+1) := by gcongr
      _≤_ := by nlinarith only [hS]
  have hi := Runtime.initializeCost_le r.call r.selected.1 r.retainedWitness S hS hprep hr
  have hf := StageGamma.readFieldsCost_le r.sourceValues S
    (fun v hv=>(r.value_bits v hv).trans hword)
  change StageGamma.readFieldsCost r.sourceValues≤6*(30*S+33)+1 at hf
  have hS3 : S≤S^3 := Nat.le_self_pow (by decide) _
  have h03 : 1≤S^3 := Nat.pow_pos hS
  unfold MomentRequest.readSteps
  rw [prepWord_eq_compact r.dispatched]
  change initializeCost r.call r.selected.1 r.retainedWitness
    (compactInput r.call r.selected.1 r.retainedWitness).length+
    StageGamma.readFieldsCost r.sourceValues+120≤110000*S^3
  omega

/-- `prop:time`, paper/paper.tex: the actual
structural frontend's source clock is cubic in its arity-only runtime
scale, including all copied source fields and finite callee reserves. -/
theorem MomentRequest.frontendSteps_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.frontendSteps≤120000*r.runtimeScale^3 := by
  let S := r.runtimeScale
  have hS : 1≤S := by have hh := r.runtimeScale_basic.1; omega
  have hword : r.word.length≤S := r.runtimeScale_basic.2.2
  have hprep := r.prep_length_le.trans hword
  have hL : (momentSourceSizes B1 B2).Lk (leadOnes r.word)≤S := by
    rw [show leadOnes r.word=1+natBitLength r.call.n by simpa only [List.append_nil] using r.source_header []]
    dsimp only [S,MomentRequest.runtimeScale]
    omega
  have hB : (momentSourceSizes B1 B2).Bk (leadOnes r.word)≤S := by
    rw [show leadOnes r.word=1+natBitLength r.call.n by simpa only [List.append_nil] using r.source_header []]
    dsimp only [S,MomentRequest.runtimeScale]
    omega
  have hr := r.readSteps_le
  change r.readSteps≤110000*S^3 at hr
  have hS3 : S≤S^3 := Nat.le_self_pow (by decide) _
  have h03 : 1≤S^3 := Nat.pow_pos hS
  change r.readSteps+9*(Program.prepWord B1 B2 r.call r.witness).length+
    6*(40*r.word.length+43)+8*((89*(Program.prepWord B1 B2 r.call r.witness).length+
      (momentSourceSizes B1 B2).Lk (leadOnes r.word)+
      (momentSourceSizes B1 B2).Bk (leadOnes r.word)+180)+2)+12≤120000*S^3
  omega

end NearQuarticWires.StageCert.Tokens
