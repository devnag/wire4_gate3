import Proof.Quartic.StageCertNative.CountRun
import Proof.Quartic.StageCert.MomentSizes

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCertificateControl StageCert.Tokens

/-- `lem:print` and `prop:time`, paper/paper.tex: cold count initialization includes actual constant
setup, original source decoding and exact output framing. -/
def countProgram : St VV MM := .seq initP (StageMain.framedOutputProgram countBody)

theorem countProgram_run {B1 B2 : ℕ} (C : Ctx) (r : IndexedRequest B1 B2)
    (hin : C.inp=(zeroMoment r).word) (hw : (zeroMoment r).bodyCapacity≤C.Wd)
    (h64 : 64≤C.Wd) :
    Hs C countProgram (a0 : DS VV MM) (3*countBodySteps r+8)
      (fun z=>z.out=frame (natWord (termCount r))) := by
  unfold countProgram
  refine (Hs.seq (t2:=3*countBodySteps r+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩ := countBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hw
    (by intro store; rw [hram,hrc]; exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf := StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (natWord (termCount r))
  rw [ho,hout,List.nil_append]

noncomputable def countBodyBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  langBudget StageRecovery.packetCallee (momentSourceSizes B1 B2) VV MM (zeroMoment r).word
    (3*countBodySteps r+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed ordinary machine computes the complete
binary population/walk census from the actual first-term source. -/
noncomputable def countBodyWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) (fun r=>(zeroMoment r).word)
      (fun r=>frame (natWord (termCount r))) countBodyBudget :=
  wordFunction_of_lang (fun r=>(zeroMoment r).word) (fun r=>frame (natWord (termCount r)))
    StageRecovery.packetCallee (momentSourceSizes B1 B2) countProgram (fun r=>3*countBodySteps r+8)
    (by
      intro r
      let C:=ctxOf StageRecovery.packetCallee (momentSourceSizes B1 B2) (zeroMoment r).word
      have hw : (zeroMoment r).bodyCapacity≤C.Wd := by
        change (zeroMoment r).bodyCapacity≤
          (momentSourceSizes B1 B2).W (leadOnes (zeroMoment r).word)
        simpa only [List.append_nil] using (zeroMoment r).sizes_width []
      obtain ⟨b,n,he,hn,ho⟩ := countProgram_run C r rfl hw (momentSourceSizes_min B1 B2 _)
      exact ⟨b,n,he,ho,hn⟩)
    (by intro r; exact le_trans (by decide) (momentSourceSizes_min B1 B2 _))

noncomputable def countBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  4*(2*StageGamma.retainedCost (input:=IndexedRequest.baseWord)
    (cache:=fun _ : IndexedRequest B1 B2=>natWord 0) (budget:=zeroOrdinalBudget) r+2)+
    4*countBodyBudget r+12

/-- `sec:algorithm`, `lem:print` and `prop:time`, paper/paper.tex: the whole-test
loop receives its actual N² or N⁸ census from ONLY the original
BASE preparation and five metadata fields, with every physical
copy, parser, binary operation and framing handoff charged. -/
noncomputable def countWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (natWord (termCount r))) countBudget :=
  Program.WordFunction.pipe (firstTermSourceWordFunction B1 B2) (countBodyWordFunction B1 B2)

end NearQuarticWires.StageCertNative
