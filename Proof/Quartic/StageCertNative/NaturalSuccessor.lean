import Proof.Quartic.StageCertNative.FieldProjection
import Proof.Gates.Expand.Cost2

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

def successorValue : Fin VV:=90

/-- `lem:print`, paper/paper.tex: the successor
field width is computed by actual binary input, increment and output,
without a unary loop in its numeric magnitude. -/
def successorBody : St VV MM :=
  .seq (StageGamma.readField successorValue)
    (.seq (.op (.inc successorValue)) (StageLift.emitNaturalFields [successorValue]))

theorem successorBody_run (C : Ctx) (v : ℕ) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=natWord v) (hwidth : natBitLength v+10≤C.Wd) :
    Hs C successorBody a (100*natBitLength v+200) (fun z=>z.out=a.out++natWord (v+1)) := by
  have hv : v+1≤2^natBitLength v := lt_natBitLength v
  have hv' : v+1<2^C.Wd := hv.trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))
  have hs : v+1<2^(natBitLength v+1) := hv.trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))
  have hb : natBitLength (v+1)≤natBitLength v+2 :=
    NearCubicGates.Close.Expand.Layout.nbl_le_of_lt _ _ hs
  unfold successorBody
  refine Hx.hs (Hs.then (StageGamma.readField_spec C successorValue (by decide) (by decide)
    a hc v [] (by simpa only [List.append_nil] using hin) (by omega)) ?_)
  rintro b ⟨bv,_bi,bs,bc,_bf⟩ n0 hn0
  refine Hs.then (hs_inc C successorValue b (by rw [bv];exact hv')) ?_
  rintro d rfl n1 hn1
  let d:=b.set successorValue (v+1)
  have hd : b.set successorValue (b.env successorValue+1)=d := by rw [bv]
  rw [hd]
  have dc : Cst d := Cst.of_fr bc (Fr.set (T:=[successorValue]) b _ (by simp)) (by decide)
  refine Hs.last (StageLift.emitNaturalFields_spec C [successorValue] d dc
    (natBitLength v+2) (by intro x hx;simp only [List.mem_singleton] at hx;subst x;decide)
    (by intro x hx;simp only [List.mem_singleton] at hx;subst x;exact hb)
    (by omega) (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self)) ?_
  rintro z ⟨zo,_zs,_zc,_zf⟩ n2 hn2
  have bo : b.out=a.out := congrArg Prod.fst bs
  refine ⟨?_,?_⟩
  · simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,d,DS.set_env_self,DS.set_out,bo] using zo
  · change n2≤1*(40*(natBitLength v+2)+43)+1 at hn2
    omega

def successorProgram : St VV MM :=
  .seq initP (StageMain.framedOutputProgram successorBody)

theorem successorProgram_run (C : Ctx) (v : ℕ) (hin : C.inp=natWord v)
    (hwidth : natBitLength v+10≤C.Wd) :
    Hs C successorProgram (a0 : DS VV MM) (300*natBitLength v+608)
      (fun z=>z.out=frame (natWord (v+1))) := by
  unfold successorProgram
  refine (Hs.seq (t2:=3*(100*natBitLength v+200)+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,_,_,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=successorBody_run C v a hc
    (by simp only [hip,List.drop_zero,hin]) hwidth
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame (natWord (v+1))
  rw [ho,hout,List.nil_append]

noncomputable def successorBudget (v : ℕ) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM (natWord v)
    (300*natBitLength v+608)

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed ordinary finite-word routine computes the
canonical successor field with all binary framing and setup charged. -/
noncomputable def successorWordFunction :
    WordFunction ℕ natWord (fun v=>frame (natWord (v+1))) successorBudget :=
  StageFormulaMetadata.wordFunction_of_finite natWord (fun v=>frame (natWord (v+1)))
    StageRecovery.packetCallee successorProgram (fun v=>300*natBitLength v+608) (fun v=>by
      obtain ⟨b,n,he,hn,ho⟩:=successorProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee (natWord v)) v rfl
        (by change natBitLength v+10≤100*((natWord v).length+1)
            have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_len v
            omega)
      exact ⟨b,n,he,ho,hn⟩)

end NearQuarticWires.StageCertNative
