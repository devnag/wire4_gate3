import Proof.Quartic.StageCertNative.PrefixCapacity

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual
original source supplies every exact Tuple prefix field before any
expanded Terms field is appended. -/
def prefixBody (B1 : ℕ) : St VV MM :=
  .seq (prefixMetadataProgram B1) emitExactPrefix

noncomputable def prefixSteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  prefixMetadataSteps r+prefixOutputSteps r+1

theorem prefixBody_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=nFirstWord r)
    (hcapacity : prefixCapacity r+10≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C (prefixBody B1) a (prefixSteps r) (fun z=>z.out=a.out++exactPrefixWord r) := by
  have hcap : prefixCapacity r<2^C.Wd := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hword : (nFirstWord r).length+10≤C.Wd := by
    unfold prefixCapacity at hcapacity
    omega
  have hroom : Cells.nativeCertificateBits B1 r.moment.call.n+nativeBitsFactor B1+
      nativeBitsExponentValue B1+r.moment.call.n+r.moment.packet.degree+100<2^C.Wd := by
    unfold prefixCapacity at hcap
    omega
  unfold prefixBody
  refine (Hs.seq (t2:=prefixOutputSteps r)
    (prefixMetadataProgram_run C r a hc hin hword hroom hempty)
    fun b ⟨br,bo,bc⟩=>?_).mono (by unfold prefixSteps;omega) (fun _ h=>h)
  have hs : prefixScalarBits r+2<2^C.Wd := by
    unfold prefixCapacity at hcap
    omega
  have htwo : 2≤C.Wd := by unfold prefixCapacity at hcapacity;omega
  exact (emitExactPrefix_run C r b bc br htwo hs).mono (by omega)
    (fun z ho=>by rw [ho,bo])

/-- `lem:print`, paper/paper.tex: a cold
ordinary prefix machine initializes its own stores and frames the
literal emitted fields, including their exact source-derived values. -/
def prefixProgram (B1 : ℕ) : St VV MM :=
  .seq initP (StageMain.framedOutputProgram (prefixBody B1))

noncomputable def prefixProgramSteps {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  3*prefixSteps r+8

theorem prefixProgram_run {B1 B2 : ℕ} (C : Ctx) (r : TermJob B1 B2)
    (hin : C.inp=nFirstWord r) (hcapacity : prefixCapacity r+10≤C.Wd) :
    Hs C (prefixProgram B1) (a0 : DS VV MM) (prefixProgramSteps r)
      (fun z=>z.out=frame (exactPrefixWord r)) := by
  unfold prefixProgram
  refine (Hs.seq (t2:=3*prefixSteps r+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by unfold prefixCapacity at hcapacity;omega) Nat.lt_two_pow_self))
    ?_).mono (by unfold prefixProgramSteps;omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=prefixBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hcapacity
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (exactPrefixWord r)
  rw [ho,hout,List.nil_append]

noncomputable def prefixBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  langBudget StageRecovery.packetCallee (prefixSizes B1 B2) VV MM
    (nFirstWord r) (prefixProgramSteps r)

/-- `lem:print` and `prop:time`, paper/paper.tex: this actual fixed ordinary machine derives the exact
native prefix from literal original source, with no decoded input. -/
noncomputable def prefixWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) nFirstWord (fun r=>frame (exactPrefixWord r)) prefixBudget :=
  wordFunction_of_lang nFirstWord (fun r=>frame (exactPrefixWord r))
    StageRecovery.packetCallee (prefixSizes B1 B2) (prefixProgram B1) prefixProgramSteps
    (by
      intro r
      obtain ⟨b,n,he,hn,ho⟩:=prefixProgram_run
        (ctxOf StageRecovery.packetCallee (prefixSizes B1 B2) (nFirstWord r)) r rfl
        (prefixSizes_required r)
      exact ⟨b,n,he,ho,hn⟩)
    (by intro r;have h:=prefixSizes_required r;omega)

end NearQuarticWires.StageCertNative
