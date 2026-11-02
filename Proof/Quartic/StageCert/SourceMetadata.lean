import Proof.Quartic.StageCert.FinalWalkForm
import Proof.Quartic.StageCertTests.TestMetadata
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the original test kind persists while mask and coefficient scratch changes. -/
def sourceTestTag : Fin VV := ⟨70,by decide⟩
/-- `sec:cycle` and `lem:print`, paper/paper.tex: the original sign ordinal persists across all mask output. -/
def sourceSignOrdinal : Fin VV := ⟨71,by decide⟩
/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the literal threshold field is retained as part of the original test request. -/
def sourceTestThreshold : Fin VV := ⟨83,by decide⟩

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: read the actual five-field whole-test suffix,
after the unchanged preparation prefix has been physically consumed. -/
def readSourceMetadata : St VV MM :=
  .seq (StageRecovery.readVariable sourceTestTag)
    (.seq (StageRecovery.readVariable selectedCircuit)
      (.seq (StageRecovery.readVariable sourceSignOrdinal)
        (.seq (StageRecovery.readVariable requestedChainRow)
          (StageRecovery.readVariable sourceTestThreshold))))

private theorem afterNatField {C : Ctx} {a b : DS VV MM} {value : ℕ} {rest : List Bool}
    (hin : C.inp.drop a.ip=natWord value++rest)
    (hb : b.ip=a.ip+(natWord value).length) : C.inp.drop b.ip=rest := by
  rw [hb,←List.drop_drop,hin]
  simp

/-- `sec:algorithm`, `lem:print` and `prop:time`, paper/paper.tex: the whole-test metadata
comes from its literal finite source bytes. No decoded test indices,
threshold, sign pattern, circuit index or source cursor is supplied. -/
theorem readSourceMetadata_run (C : Ctx) (metadata : StageCertTests.TestMetadata)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=metadata.word++rest)
    (hwidth : ∀v∈[metadata.tag,metadata.circuit,metadata.signOrdinal,metadata.digitOrdinal,metadata.threshold],
      natBitLength v+2≤C.Wd) :
    Hs C readSourceMetadata a
      (30*(natBitLength metadata.tag+natBitLength metadata.circuit+natBitLength metadata.signOrdinal+
        natBitLength metadata.digitOrdinal+natBitLength metadata.threshold)+164) (fun z=>
      z.env sourceTestTag=metadata.tag ∧ z.env selectedCircuit=metadata.circuit ∧
      z.env sourceSignOrdinal=metadata.signOrdinal ∧ z.env requestedChainRow=metadata.digitOrdinal ∧
      z.env sourceTestThreshold=metadata.threshold ∧ z.ip=a.ip+metadata.word.length ∧
      (z.out,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.out,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z ([sourceTestTag,selectedCircuit,sourceSignOrdinal,requestedChainRow,sourceTestThreshold]++rdNatT)) := by
  have hinput : C.inp.drop a.ip=natWord metadata.tag++
      (natWord metadata.circuit++(natWord metadata.signOrdinal++(natWord metadata.digitOrdinal++
        (natWord metadata.threshold++rest)))) := by
    simpa only [StageCertTests.TestMetadata.word,List.append_assoc] using hin
  unfold readSourceMetadata
  apply Hx.hs
  refine Hs.then (StageRecovery.readVariable_spec C a hc sourceTestTag (by decide) (by decide)
    metadata.tag _ hinput (hwidth _ (by simp)))
    (fun b ⟨bt,bi,bs,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (StageRecovery.readVariable_spec C b bc selectedCircuit (by decide) (by decide)
    metadata.circuit _ (afterNatField hinput bi) (hwidth _ (by simp)))
    (fun d ⟨dj,di,ds,dc,dfr⟩ n2 hn2=>?_)
  refine Hs.then (StageRecovery.readVariable_spec C d dc sourceSignOrdinal (by decide) (by decide)
    metadata.signOrdinal _ (afterNatField (afterNatField hinput bi) di) (hwidth _ (by simp)))
    (fun e ⟨es,ei,er,ec,efr⟩ n3 hn3=>?_)
  refine Hs.then (StageRecovery.readVariable_spec C e ec requestedChainRow (by decide) (by decide)
    metadata.digitOrdinal _ (afterNatField (afterNatField (afterNatField hinput bi) di) ei)
    (hwidth _ (by simp)))
    (fun f ⟨fr,fi,fs,fc,ffr⟩ n4 hn4=>?_)
  refine Hs.last (StageRecovery.readVariable_spec C f fc sourceTestThreshold (by decide) (by decide)
    metadata.threshold rest (afterNatField (afterNatField (afterNatField (afterNatField hinput bi) di) ei) fi)
    (hwidth _ (by simp)))
    (fun z ⟨zt,zi,zs,zc,zfr⟩ n5 hn5=>?_)
  refine ⟨⟨?_,?_,?_,?_,zt,?_,zs.trans (fs.trans (er.trans (ds.trans bs))),zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans ((efr.weaken (by decide)).trans
      ((ffr.weaken (by decide)).trans (zfr.weaken (by decide)))))⟩,?_⟩
  · rw [zfr _ (by decide),ffr _ (by decide),efr _ (by decide),dfr _ (by decide)]
    exact bt
  · rw [zfr _ (by decide),ffr _ (by decide),efr _ (by decide)]
    exact dj
  · rw [zfr _ (by decide),ffr _ (by decide)]
    exact es
  · rw [zfr _ (by decide)]
    exact fr
  · simp only [StageCertTests.TestMetadata.word,List.length_append]
    omega
  · omega

end NearQuarticWires.StageCert.Tokens
