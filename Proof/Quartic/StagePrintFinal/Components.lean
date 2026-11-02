import Proof.Quartic.StagePrintFinal.Native
import Proof.Quartic.StagePrintFinal.Bounds
import Proof.Quartic.StageCompiledTerms.Cost

/-!
# Exact physical components of the complete printer pipeline

Paper: `lem:print` and `prop:time`,
paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StagePrint

/-- `lem:print`, paper/paper.tex: the
actual recovery modulus is retained through both middle-record maps. -/
def modulus {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ := r.prime^r.child.selected.1.e

/-- `lem:print`, paper/paper.tex: both
middle-record maps retain the same original-column target count. -/
noncomputable def targetCount {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ := r.child.cellCall.ncol

/-- `lem:print`, paper/paper.tex: one
actual carrier envelope and whole-cut collector are followed by two
physical metadata-preserving maps. Every program and its own budget
remain paired; the header and native data are the actual closed ones. -/
structure Components (B1 B2 : ℕ) where
  envelope : CarrierEnvelope.Producer B1 B2
  collector : GreedyCollector.Producer B1 B2
  collectedMap : NativeMiddle.Mapper collector.2 (modulus (B1:=B1) (B2:=B2)) targetCount
  headerMap : NativeMiddle.Mapper (headerWordFunction B1 B2) modulus targetCount

/-- `prop:time`, paper/paper.tex: the
four ordinary sequential compositions charge their actual five stage
budgets with the literal fixed composition factors. -/
def composeBudget (a b c d e : ℕ) : ℕ :=
  4*(4*(4*(4*a+4*b+12)+4*c+12)+4*d+12)+4*e+12

/-- `prop:time`, paper/paper.tex: only
the original upstream source stage contributes the additive raw-index
cost; every physical composition multiplier is an absolute constant. -/
theorem composeBudget_eq (a b c d e : ℕ) :
    composeBudget a b c d e=256*a+256*b+64*c+16*d+4*e+1020 := by
  unfold composeBudget
  ring

/-- `prop:time`, paper/paper.tex: the
complete printer budget is exactly the real compiler, envelope, two
actual middle maps and actual native recovery composition budget. -/
noncomputable def budget
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ}
    (S : Components B1 B2) (r : Greedy.PrintRequest B1 B2) : ℕ :=
  composeBudget ((StageCompiledTerms.compiledTermsProducer B1 B2).1 r) (S.envelope.1 r)
    (S.collectedMap.budget r) (S.headerMap.budget r) ((native r).recoveryBudget h)

/-- `lem:print`, paper/paper.tex: the
first actual middle map consumes exactly the one retained original
carrier envelope, preserving both original metadata codecs. -/
noncomputable def collectedWordFunction {B1 B2 : ℕ} (S : Components B1 B2) :
    WordFunction (Greedy.PrintRequest B1 B2) CarrierEnvelope.word
      (fun r=>frame (NativeMiddle.word (modulus r) (GreedyCollector.word r) (targetCount r)))
      S.collectedMap.budget := S.collectedMap.machine

/-- `lem:print`, paper/paper.tex: the
second actual middle map constructs exactly the native recovery
request, including its original modulus, table and target count. -/
noncomputable def nativeWordFunction {B1 B2 : ℕ} (S : Components B1 B2) :
    WordFunction (Greedy.PrintRequest B1 B2)
      (fun r=>NativeMiddle.word (modulus r) (GreedyCollector.word r) (targetCount r))
      (fun r=>frame (native r).word) S.headerMap.budget where
  program:=S.headerMap.machine.program
  realizes r:=by
    obtain ⟨receipt,hr,ho⟩:=S.headerMap.machine.realizes r
    refine ⟨receipt,hr,?_⟩
    rw [←native_word_eq r]
    exact ho

/-- `lem:print`, `lem:residue` and `prop:time`, paper/paper.tex: the literal four-pipe
composition starts at the original Greedy input and prints precisely
its RAW centered table. Each stage executes its actual physical
program, preserving all bad-witness and original-column values. -/
noncomputable def wordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) {B1 B2 : ℕ} (S : Components B1 B2) :
    WordFunction (Greedy.PrintRequest B1 B2) Greedy.printInput
      (fun r=>listWord intWord (Greedy.printTable r)) (budget h S) := by
  let f1:=Program.WordFunction.pipe (StageCompiledTerms.compiledTermsProducer B1 B2).2 S.envelope.2
  let f2:=Program.WordFunction.pipe f1 (collectedWordFunction S)
  let f3:=Program.WordFunction.pipe f2 (nativeWordFunction S)
  exact Program.WordFunction.pipe f3 (recoveryWordFunction h B1 B2)

end NearQuarticWires.StagePrintFinal
