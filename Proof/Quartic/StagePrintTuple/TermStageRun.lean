import Proof.Quartic.StagePrintTuple.TermStageProgram

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP

/-- `lem:print` and `prop:time`, paper/paper.tex: one genuine original monomial is physically read,
prepared, expanded through its original child tuples and stacked with
its signed coefficient, yielding exactly the next complete Terms state. -/
theorem termStageRun {B : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B)
    (span : ℕ) (hn : native.program.tapeCount ≤ span)
    (hcoef : coefficientWordFunction.program.tapeCount ≤ span)
    (hs : supportIndexWordFunction.program.tapeCount ≤ span)
    (ht : tupleRecordPrinter.program.tapeCount ≤ span)
    (hstack : stackRecordPrinter.program.tapeCount ≤ span)
    (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) (cap : ℕ)
    (hcap : termStageCapacity B r k hk ≤ cap) :
    ∃τ,WXExec cap (termStageProgram native span hn hcoef hs ht hstack)
      (((r.progressData k).state span r).setv 17 (r.terms.length-(k+1))) τ
      (termStageCost B r k hk) ∧ SimW ((r.progressData (k+1)).state span r) τ := by
  let support : List ℕ := ((r.terms[k]'hk).1.sort (·≤·)).map Fin.val
  let coefficient : ℤ := (r.terms[k]'hk).2
  let data := r.progressMonomial k hk
  let t := r.terms[k]'hk
  have hm : t∈r.terms := List.getElem_mem hk
  let a := monomialLocalCapacity (r.stackWidth+1) support coefficient
  let b := monomialPrepareCapacity (r.stackWidth+1) support coefficient
  let c := reverseLoopCapacity B r data
  let d := 100000000*(monomialFinishMagnitude r data t hm+data.output.length+1)
  have four (x y z w : ℕ) : x ≤ x+y+z+w ∧ y ≤ x+y+z+w ∧
      z ≤ x+y+z+w ∧ w ≤ x+y+z+w := by omega
  have hsum : a+b+c+d ≤ cap := hcap
  have hf := four a b c d
  have ea := kernelMonomialSource_run r span k cap hk (hf.1.trans hsum)
  obtain ⟨sb,eb,hb⟩ := kernelMonomialPrepare_run r span k cap hk hcoef (hf.2.1.trans hsum)
  obtain ⟨sc,ec,hc'⟩ := reverseLoop_run native r data span cap hn hs ht (hf.2.2.1.trans hsum) sb hb
  obtain ⟨sd,ed,hd⟩ := StageTupleMonomialFinish.monomialFinishProgram_spec span hstack cap r data t hm
    rfl rfl (hf.2.2.2.trans hsum)
  obtain ⟨d',ed',hd'⟩ := wxexec_sim ed sc hc'
  have hpost : (data.finishedData r t hm).state span r=(r.progressData (k+1)).state span r :=
    congrArg (fun v : KernelData=>v.state span r) (r.progress_finished k hk)
  rw [hpost] at hd
  refine ⟨d',?_,SimW.trans hd hd'⟩
  simpa only [termStageProgram,termStageCost] using ea.seq (eb.seq (ec.seq ed'))

end NearQuarticWires.StageTuple
