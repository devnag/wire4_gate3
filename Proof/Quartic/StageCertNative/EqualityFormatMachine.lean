import Proof.Quartic.StageCertNative.EqualityFormatBody
import Proof.Quartic.StageCertNative.EntryFormatJoin
import Proof.Quartic.StageCertNative.TermNative

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

noncomputable def equalityEntryWord {B1 B2 : ℕ} (r : TermJob B1 B2) : List Bool :=
  (exactEntry r.moment).word++frame (termRequest r.base r.index).output

noncomputable def equalitySizes (B1 B2 : ℕ) : Sz :=
  StageEntryAllocation.sizes (entrySizingCoefficient B1 B2) (entrySizingExponent B1 B2)

/-- `lem:print` and `prop:time`, paper/paper.tex: a copied finite equality stream requires no larger
arithmetic allocation than its actual original source and packed width. -/
theorem equalitySizes_required {B1 B2 : ℕ} (r : TermJob B1 B2) :
    (exactEntry r.moment).sizingMagnitude+10≤
      (equalitySizes B1 B2).W (leadOnes (equalityEntryWord r)) := by
  have hh : leadOnes (equalityEntryWord r)=leadOnes (boundedExactEntry r).word := by
    rw [StageEntryAllocation.original_header]
    unfold equalityEntryWord StagePrint.EntryFormat.Request.word
    simp only [List.append_assoc]
    exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  rw [hh]
  exact StageEntryAllocation.required_width (entrySizingCoefficient B1 B2)
    (entrySizingExponent B1 B2) false (boundedExactEntry r)

/-- `lem:print`, paper/paper.tex: the literal
finite equality-source adapter initializes all stores and frames the
raw stream together with its two actually computed unary dimensions. -/
def equalityFormatProgram : St VV MM :=
  .seq initP (StageMain.framedOutputProgram equalityFormatBody)

noncomputable def equalityProgramSteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  3*equalityFormatSteps (exactEntry r.moment) (termRequest r.base r.index).output+8

theorem equalityFormatProgram_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (hin : C.inp=equalityEntryWord r)
    (hsize : (exactEntry r.moment).sizingMagnitude+10≤C.Wd) :
    Hs C equalityFormatProgram (a0 : DS VV MM) (equalityProgramSteps r)
      (fun z=>z.out=frame (StagePrint.Downstream.equalityRowsInput (termNativeRequest r))) := by
  let e:=exactEntry r.moment
  let raw:=(termRequest r.base r.index).output
  have hf:=StagePrint.EntryFormat.inputFits_of_sizing C e hsize
  have htwo : 2<2^C.Wd :=
    lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hf.wordWidth)
  unfold equalityFormatProgram
  refine (Hs.seq (t2:=3*equalityFormatSteps e raw+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl htwo) ?_).mono
      (by change 5+(3*equalityFormatSteps e raw+2)+1≤3*equalityFormatSteps e raw+8;omega)
      (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=equalityFormatBody_run C e raw a hc
    (by simp only [hip,List.drop_zero,hin];rfl)
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩) hf
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have heframe:=StageMain.framedOutput_run he
  rw [hm] at heframe
  refine ⟨{b with out:=frame b.out},3*n+2,heframe,by omega,?_⟩
  change frame b.out=frame (StagePrint.Downstream.equalityRowsInput (termNativeRequest r))
  rw [ho,hout,List.nil_append]
  congr 1
  unfold StagePrint.Downstream.equalityRowsInput
  dsimp only [termNativeRequest]
  rw [StagePrint.nativeEqualityCuts_word]
  rw [StagePrint.native_width_eq_half]
  rfl

noncomputable def equalityFormatBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  langBudget StageRecovery.packetCallee (equalitySizes B1 B2) VV MM
    (equalityEntryWord r) (equalityProgramSteps r)

/-- `lem:print` and `prop:time`, paper/paper.tex: this actual source adapter has no equality census,
native width, header, pool or decoded context as a runtime input. -/
noncomputable def equalityInputWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) equalityEntryWord
      (fun r=>frame (StagePrint.Downstream.equalityRowsInput (termNativeRequest r)))
      equalityFormatBudget :=
  wordFunction_of_lang equalityEntryWord
    (fun r=>frame (StagePrint.Downstream.equalityRowsInput (termNativeRequest r)))
    StageRecovery.packetCallee (equalitySizes B1 B2) equalityFormatProgram equalityProgramSteps
    (by
      intro r
      obtain ⟨b,n,he,hn,ho⟩:=equalityFormatProgram_run
        (ctxOf StageRecovery.packetCallee (equalitySizes B1 B2) (equalityEntryWord r)) r rfl
        (equalitySizes_required r)
      exact ⟨b,n,he,ho,hn⟩)
    (by intro r;have hh:=equalitySizes_required r;omega)

end NearQuarticWires.StageCertNative
