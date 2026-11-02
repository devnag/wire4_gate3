import Proof.Quartic.StageCert.MomentSizes
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain

/-- `lem:print` and `prop:time`, paper/paper.tex: an ordinary cold program initializes its numeric state
and frames the complete exact signed moment packet for the next stage. -/
def momentBodyProgram : St VV MM := .seq initP (framedOutputProgram momentBody)

/-- `lem:print` and `prop:time`, paper/paper.tex: the full exact packet is produced from the actual finite
frontend output, without any initialized records or supplied Formula. -/
theorem momentBodyProgram_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (hin : C.inp=r.flaggedWord) (hwidth : r.bodyCapacity≤C.Wd) (h64 : 64≤C.Wd) :
    Hs C momentBodyProgram (a0 : DS VV MM) (3*(r.readSteps+r.packetSteps+1)+8)
      (fun z=>z.out=frame r.packet.word) := by
  unfold momentBodyProgram
  refine (Hs.seq (t2 := 3*(r.readSteps+r.packetSteps+1)+2)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,hkout,hkc,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  have hKC : a.kc≤a.kout.length := by rw [hkc,hkout]; exact le_rfl
  obtain ⟨b,n,he,hn,ho,_,_⟩ := momentBody_run C r [] a hc
    (by simp only [hip,List.drop_zero,hin,List.append_nil]) hwidth
    (by intro store; rw [hram,hrc]; exact ⟨rfl,rfl⟩) hKC
  have hm : markOutputState a=a := by
    unfold markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf := framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame r.packet.word
  rw [ho,hout,List.nil_append]

/-- `prop:time`, paper/paper.tex: the actual
ordinary-machine budget includes compiled binary operations, setup,
output writes, memory head restoration and every finite source scan. -/
noncomputable def MomentRequest.bodyBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  langBudget (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) VV MM r.flaggedWord
    (3*(r.readSteps+r.packetSteps+1)+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed ordinary machine emits the exact q=0
signed moment packet from every actual computed-flag source. -/
noncomputable def momentBodyWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.flaggedWord
      (fun r=>frame r.packet.word) MomentRequest.bodyBudget :=
  wordFunction_of_lang MomentRequest.flaggedWord (fun r=>frame r.packet.word)
    (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) momentBodyProgram
    (fun r=>3*(r.readSteps+r.packetSteps+1)+8) (by
      intro r
      have hw : r.bodyCapacity≤(momentSourceSizes B1 B2).W (leadOnes r.flaggedWord) := by
        simpa only [MomentRequest.flaggedWord] using
          r.sizes_width (structuralFlagList r (momentFlagEdges r.test))
      obtain ⟨b,n,he,hn,ho⟩ := momentBodyProgram_run
        (ctxOf (structuralSourceCallee B1 B2) (momentSourceSizes B1 B2) r.flaggedWord)
        r rfl hw (momentSourceSizes_min B1 B2 _)
      exact ⟨b,n,he,ho,hn⟩) (by
      intro r
      exact le_trans (by decide) (momentSourceSizes_min B1 B2 _))

end NearQuarticWires.StageCert.Tokens
