import Proof.Quartic.StageFormulaMetadata.Packet
import Proof.Quartic.StageRecovery.PacketFields
import Proof.Quartic.StageCertTests.MetadataEmit

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open StageRecovery (readVariable readVariable_spec modulusVar)

/-- `lem:print`, paper/paper.tex: original
packet scalars have retained registers outside all token scratch. -/
def rawIndexVar : Fin VV := 105
def rawDegreeVar : Fin VV := 103
def rawArityVar : Fin VV := 104

/-- `lem:print`, paper/paper.tex: the four
actual raw header fields are decoded in their unchanged byte order. -/
def readRawHeader : St VV MM :=
  .seq (readVariable rawIndexVar)
    (.seq (readVariable rawDegreeVar)
      (.seq (readVariable modulusVar) (readVariable rawArityVar)))

/-- `prop:time`, paper/paper.tex: the source
clock prices all four physically read natural fields and sequencing. -/
def rawHeaderCost (packet : RawWalkPacket) : ℕ :=
  30*(packet.header.map natBitLength).sum+131

/-- `lem:print`, paper/paper.tex: the actual
four-field parser preserves its arbitrary following framed payload
and all source stores, without receiving decoded header values. -/
theorem readRawHeader_spec (C : Ctx) (packet : RawWalkPacket) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=packet.header.flatMap natWord++rest)
    (hwidth : ∀ value∈packet.header,natBitLength value+2≤C.Wd) :
    Hs C readRawHeader a (rawHeaderCost packet) (fun b=>
      b.env rawIndexVar=packet.index ∧ b.env rawDegreeVar=packet.degree ∧
      b.env modulusVar=packet.modulus ∧ b.env rawArityVar=packet.arity ∧
      b.ip=a.ip+(packet.header.flatMap natWord).length ∧
      (b.out,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.out,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b ([rawIndexVar,rawDegreeVar,modulusVar,rawArityVar]++rdNatT)) := by
  have hinput : C.inp.drop a.ip=natWord packet.index++natWord packet.degree++
      natWord packet.modulus++natWord packet.arity++rest := by
    simpa only [RawWalkPacket.header,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.append_assoc] using hin
  unfold readRawHeader
  refine (Hs.seq (t2:=30*natBitLength packet.degree+30*natBitLength packet.modulus+
    30*natBitLength packet.arity+98)
    (readVariable_spec C a hc rawIndexVar (by decide) (by decide) packet.index _
      (by simpa only [List.append_assoc] using hinput)
      (hwidth _ (by simp [RawWalkPacket.header])))
    fun b ⟨hbv,hbi,hbr,hbc,hbf⟩=>?_).mono
      (by simp [rawHeaderCost,RawWalkPacket.header];omega) (fun _ h=>h)
  have hbin : C.inp.drop b.ip=natWord packet.degree++natWord packet.modulus++natWord packet.arity++rest := by
    rw [hbi,←List.drop_drop,hinput]
    simp only [List.append_assoc,List.drop_left]
  refine (Hs.seq (t2:=30*natBitLength packet.modulus+30*natBitLength packet.arity+65)
    (readVariable_spec C b hbc rawDegreeVar (by decide) (by decide) packet.degree _
      (by simpa only [List.append_assoc] using hbin)
      (hwidth _ (by simp [RawWalkPacket.header])))
    fun d ⟨hdv,hdi,hdr,hdc,hdf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hdin : C.inp.drop d.ip=natWord packet.modulus++natWord packet.arity++rest := by
    rw [hdi,←List.drop_drop,hbin]
    simp only [List.append_assoc,List.drop_left]
  refine (Hs.seq (t2:=30*natBitLength packet.arity+32)
    (readVariable_spec C d hdc modulusVar (by decide) (by decide) packet.modulus _
      (by simpa only [List.append_assoc] using hdin)
      (hwidth _ (by simp [RawWalkPacket.header])))
    fun e ⟨hev,hei,her,hec,hef⟩=>?_).mono (by omega) (fun _ h=>h)
  have hein : C.inp.drop e.ip=natWord packet.arity++rest := by
    rw [hei,←List.drop_drop,hdin]
    simp only [List.append_assoc,List.drop_left]
  refine (readVariable_spec C e hec rawArityVar (by decide) (by decide) packet.arity rest hein
    (hwidth _ (by simp [RawWalkPacket.header]))).mono le_rfl ?_
  rintro last ⟨hlv,hli,hlr,hlc,hlf⟩
  refine ⟨?_,?_,?_,hlv,?_,hlr.trans (her.trans (hdr.trans hbr)),hlc,?_⟩
  · rw [hlf _ (by decide),hef _ (by decide),hdf _ (by decide),hbv]
  · rw [hlf _ (by decide),hef _ (by decide),hdv]
  · rw [hlf _ (by decide),hev]
  · rw [hli,hei,hdi,hbi]
    simp only [RawWalkPacket.header,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_append]
    omega
  · exact (hbf.weaken (by decide)).trans
      ((hdf.weaken (by decide)).trans ((hef.weaken (by decide)).trans (hlf.weaken (by decide))))

end NearQuarticWires.StageFormulaMetadata
