import Proof.Quartic.StageCert.MomentBodyMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain

/-- `def:mask` and `prop:time`, paper/paper.tex: one uniform bound pays the actual eight edge calls,
including complete prep copies and both binary pattern fields. -/
noncomputable def MomentRequest.frontendSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  let L := (momentSourceSizes B1 B2).Lk (leadOnes r.word)
  let B := (momentSourceSizes B1 B2).Bk (leadOnes r.word)
  let P := (Program.prepWord B1 B2 r.call r.witness).length
  r.readSteps+9*P+6*(40*r.word.length+43)+8*((89*P+L+B+180)+2)+12

/-- `def:mask` and `lem:print`, paper/paper.tex: the ordinary source initializes cold state and frames
the identical original source extended by its actually computed flags. -/
def momentFrontendProgram : St VV MM := .seq initP (framedOutputProgram momentFrontend)

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: the actual fixed source
program computes every required flag from original bytes and a real
ordinary structural callee. All reserves are derived from the source. -/
theorem momentFrontendProgram_run {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Hs (ctxOf (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) r.word)
      momentFrontendProgram (a0 : DS VV MM) (3*r.frontendSteps+8)
      (fun z=>z.out=frame r.flaggedWord) := by
  let C := ctxOf (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) r.word
  let L := (momentSourceSizes B1 B2).Lk (leadOnes r.word)
  let B := (momentSourceSizes B1 B2).Bk (leadOnes r.word)
  let P := (Program.prepWord B1 B2 r.call r.witness).length
  have h64 : 64≤C.Wd := momentSourceSizes_min B1 B2 _
  have hw : r.bodyCapacity≤C.Wd := by
    change r.bodyCapacity≤(momentSourceSizes B1 B2).W (leadOnes r.word)
    simpa only [List.append_nil] using r.sizes_width []
  have hcwidth := (r.body_capacity C.Wd hw).source
  have hcost : ∀edge,9*P+40*natBitLength (r.edgeRequest edge).left.val+
      40*natBitLength (r.edgeRequest edge).right.val+L+B+180≤89*P+L+B+180 := by
    intro edge
    have hh := StageMainMask.structural_index_bits (r.edgeRequest edge)
    change natBitLength (r.edgeRequest edge).left.val≤P ∧
      natBitLength (r.edgeRequest edge).right.val≤P at hh
    omega
  unfold momentFrontendProgram
  refine (Hs.seq (t2 := 3*r.frontendSteps+2)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,hkin,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho,_,_⟩ := momentFrontend_run r C.Wd r.word L B (89*P+L+B+180)
    r.sizes_input r.sizes_callee hcost [] a hc hkin
    (by simp only [hip,List.drop_zero,List.append_nil]) hcwidth
    (by intro store; rw [hram,hrc]; exact ⟨rfl,rfl⟩)
  have hm : markOutputState a=a := by
    unfold markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf := framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,?_,?_⟩
  · change n≤r.frontendSteps at hn
    omega
  · change frame b.out=frame r.flaggedWord
    rw [ho,hout,List.nil_append]

/-- `prop:time`, paper/paper.tex: the actual
frontend machine clock includes binary compilation, finite structural
calls, literal source rewrites and restoration of every memory head. -/
noncomputable def MomentRequest.frontendBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  langBudget (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) VV MM r.word
    (3*r.frontendSteps+8)

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: one fixed ordinary
machine computes the actual one/eight structural-source suffix from
the original finite source, without any flag-provider premise. -/
noncomputable def momentFrontendWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>frame r.flaggedWord) MomentRequest.frontendBudget :=
  wordFunction_of_lang MomentRequest.word (fun r=>frame r.flaggedWord)
    (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) momentFrontendProgram
    (fun r=>3*r.frontendSteps+8) (by
      intro r
      obtain ⟨b,n,he,hn,ho⟩ := momentFrontendProgram_run r
      exact ⟨b,n,he,ho,hn⟩) (by
      intro r
      exact le_trans (by decide) (momentSourceSizes_min B1 B2 _))

end NearQuarticWires.StageCert.Tokens
