import Proof.Quartic.StageCertNative.CachedSource
import Proof.Quartic.StageGamma.ReadFields
import Proof.Quartic.StageLift.RawHeader

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the pool reads
its actual once-computed binary count from its retained internal source. -/
def cachedCountBody : St VV MM :=
  .seq (StageGamma.readField termRemaining) (StageLift.emitNaturalFields [termRemaining])

noncomputable def cachedCountSteps {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  70*natBitLength (termCount r)+80

theorem cachedCountBody_run {B1 B2 : ℕ} (C : Ctx) (r : IndexedRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=cachedSourceWord r)
    (hwidth : natBitLength (termCount r)+4≤C.Wd) :
    Hs C cachedCountBody a (cachedCountSteps r) (fun z=>z.out=a.out++natWord (termCount r)) := by
  unfold cachedCountBody
  apply Hx.hs
  refine Hs.then (StageGamma.readField_spec C termRemaining (by decide) (by decide)
    a hc (termCount r) (r.baseWord++StagePrint.Context.word r.prepared)
    (by simpa only [cachedSourceWord,List.append_assoc] using hin) (by omega))
    (fun b ⟨bv,_bi,bs,bc,_bf⟩ n1 hn1=>?_)
  refine Hs.last (StageLift.emitNaturalFields_spec C [termRemaining] b bc
    (natBitLength (termCount r)) (by intro x hx;simp only [List.mem_singleton] at hx;subst x;decide)
    (by intro x hx;simp only [List.mem_singleton] at hx;subst x;rw [bv]) (by omega)
    (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self))
    (fun z ⟨zo,_zs,_zc,_zf⟩ n2 hn2=>?_)
  have bo : b.out=a.out := congrArg Prod.fst bs
  refine ⟨?_,?_⟩
  · simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,bv,bo] using zo
  · change n2≤1*(40*natBitLength (termCount r)+43)+1 at hn2
    dsimp only [cachedCountSteps]
    omega

def cachedCountProgram : St VV MM :=
  .seq initP (StageMain.framedOutputProgram cachedCountBody)

theorem cachedCountProgram_run {B1 B2 : ℕ} (C : Ctx) (r : IndexedRequest B1 B2)
    (hin : C.inp=cachedSourceWord r) (hwidth : natBitLength (termCount r)+4≤C.Wd) :
    Hs C cachedCountProgram (a0 : DS VV MM) (3*cachedCountSteps r+8)
      (fun z=>z.out=frame (natWord (termCount r))) := by
  unfold cachedCountProgram
  refine (Hs.seq (t2:=3*cachedCountSteps r+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,_,_,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=cachedCountBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hwidth
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (natWord (termCount r))
  rw [ho,hout,List.nil_append]

noncomputable def cachedCountBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM (cachedSourceWord r)
    (3*cachedCountSteps r+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed ordinary reader supplies the exact original
N²/N⁸ loop count from the actual retained source, charging binary
reads/writes, source measurement, allocation and output framing. -/
noncomputable def cachedCountWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) cachedSourceWord
      (fun r=>frame (natWord (termCount r))) cachedCountBudget :=
  StageFormulaMetadata.wordFunction_of_finite cachedSourceWord
    (fun r=>frame (natWord (termCount r))) StageRecovery.packetCallee
    cachedCountProgram (fun r=>3*cachedCountSteps r+8) (fun r=>by
      have hb:=NearCubicGates.Close.Dispatch.natBitLength_le_len (termCount r)
      obtain ⟨b,n,he,hn,ho⟩:=cachedCountProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee (cachedSourceWord r)) r rfl
        (by change natBitLength (termCount r)+4≤100*((cachedSourceWord r).length+1)
            dsimp only [cachedSourceWord]
            simp only [List.length_append]
            omega)
      exact ⟨b,n,he,ho,hn⟩)

end NearQuarticWires.StageCertNative
