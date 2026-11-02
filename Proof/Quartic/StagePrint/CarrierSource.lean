import Proof.Quartic.StagePrint.CompactHeader
import Proof.Quartic.StageMain.CompactInitialize
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Carrier
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift

/-- Step 3 and `lem:print`, paper/paper.tex: the retained finite context consists of the original call, selected parameters and actual witness prefix. -/
def preparedWord (r : Header.HeaderCall) : List Bool :=
  StageMain.Compact.compactInput r.call r.parameters
    (Program.witnessPrefix r.call r.parameters r.witness)

/-- Step 3 and `lem:print`, paper/paper.tex: one measured finite preparation precedes the original counted term stream. -/
def sourcePrefix (r : Header.HeaderCall) (count : ℕ) : List Bool :=
  natWord (preparedWord r).length ++ preparedWord r ++ natWord count

/-- `lem:print`, paper/paper.tex: the measured source length is read before the existing physical finite-source acquisition and the actual term count. -/
def lengthVar : Fin VV := 75
def countVar : Fin VV := 55
def readContext : St VV MM :=
  .seq (StageRecovery.readVariable lengthVar)
    (.seq StageMain.Compact.initializeCompact (StageRecovery.readVariable countVar))

/-- `prop:time`, paper/paper.tex: both literal natural fields, every finite-source bit and every sequence transition are paid. -/
def contextCost (r : Header.HeaderCall) (count B : ℕ) : ℕ :=
  30*natBitLength (preparedWord r).length+32+1+
    (StageMain.Compact.initializeCost r.call r.parameters
      (Program.witnessPrefix r.call r.parameters r.witness) B+1+(30*natBitLength count+32))

/-- `lem:print`, paper/paper.tex: the real once-only source prefix is retained and decoded before the first term packet, with no supplied call, header or source table. -/
theorem readContext_run (C : Ctx) (r : Header.HeaderCall) (count B : ℕ)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=sourcePrefix r count++rest)
    (hP : natBitLength (preparedWord r).length+2≤ C.Wd)
    (hN : natBitLength count+2≤ C.Wd)
    (hW : (StageLift.preparedPrefixWord r.call r.parameters).length+2≤ C.Wd)
    (hcap : (preparedWord r).length<2^C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields r.parameters ++ r.parameters.primes.sort (· ≤ ·) ++
      parameterTailFields r.parameters ++ r.parameters.factors,natBitLength value≤ B)
    (hB : B+2≤ C.Wd)
    (hcounts : r.parameters.primes.card<2^C.Wd ∧ r.parameters.factors.length<2^C.Wd)
    (hempty : ∀ store ∈ StageMain.Compact.compactStore :: StageMain.Compact.decodeStores,
      a.ram store=[] ∧ a.rc store=0) :
    Hs C readContext a (contextCost r count B) (fun e=>
      e.ip=a.ip+(sourcePrefix r count).length ∧ e.env countVar=count ∧
      e.env StageMain.Compact.compactLength=(preparedWord r).length ∧
      e.ram StageMain.Compact.compactStore=(preparedWord r).map Bool.toNat ∧
      e.rc StageMain.Compact.compactStore=(preparedWord r).length ∧
      Header.HeaderSourceData r e ∧
      (e.out,e.kin,e.kout,e.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst e) := by
  have hinput : C.inp.drop a.ip=natWord (preparedWord r).length ++
      (preparedWord r ++ natWord count ++ rest):=by
    simpa only [sourcePrefix,List.append_assoc] using hin
  unfold readContext
  refine (Hs.seq
    (t2:=StageMain.Compact.initializeCost r.call r.parameters
      (Program.witnessPrefix r.call r.parameters r.witness) B+1+(30*natBitLength count+32))
    (StageRecovery.readVariable_spec C a hc lengthVar (by decide) (by decide)
      (preparedWord r).length _ hinput hP) ?_).mono (by unfold contextCost;omega) (fun _ h=>h)
  rintro b ⟨_hbP,hbi,hbr,hbc,_hbf⟩
  have hbram : b.ram=a.ram:=congrArg (fun t=>t.2.1) hbr
  have hbrc : b.rc=a.rc:=congrArg (fun t=>t.2.2.1) hbr
  have hbsmall : (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc):=
    congrArg (fun t=>(t.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2)) hbr
  have hbin : C.inp.drop b.ip=preparedWord r ++ (natWord count ++ rest):=by
    rw [hbi,←List.drop_drop,hinput,List.drop_left]
    simp only [List.append_assoc]
  have hbempty : ∀ store ∈ StageMain.Compact.compactStore :: StageMain.Compact.decodeStores,
      b.ram store=[] ∧ b.rc store=0:=by
    intro store hs
    rw [hbram,hbrc]
    exact hempty store hs
  refine (Hs.seq (t2:=30*natBitLength count+32)
    (StageMain.Compact.initialize_run C r.call r.parameters B
      (Program.witnessPrefix r.call r.parameters r.witness) (natWord count++rest)
      b hbc hbin hW hcap hwidth hB hcounts hbempty) ?_).mono (by omega) (fun _ h=>h)
  rintro d ⟨hdi,hddata,hdlen,hdram,hdrc,hdsmall,hdc,_hdfr⟩
  change d.ip=b.ip+(preparedWord r).length at hdi
  change d.env StageMain.Compact.compactLength=(preparedWord r).length at hdlen
  change d.ram StageMain.Compact.compactStore=(preparedWord r).map Bool.toNat at hdram
  change d.rc StageMain.Compact.compactStore=(preparedWord r).length at hdrc
  have hdin : C.inp.drop d.ip=natWord count++rest:=by
    rw [hdi,←List.drop_drop,hbin,List.drop_left]
  refine (StageRecovery.readVariable_spec C d hdc countVar (by decide) (by decide)
    count rest hdin hN).mono le_rfl ?_
  rintro e ⟨hen,hei,her,hec,hef⟩
  have heram : e.ram=d.ram:=congrArg (fun t=>t.2.1) her
  have herc : e.rc=d.rc:=congrArg (fun t=>t.2.2.1) her
  have hesmall : (e.out,e.kin,e.kout,e.kc)=(d.out,d.kin,d.kout,d.kc):=
    congrArg (fun t=>(t.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2)) her
  refine ⟨?_,hen,?_,?_,?_,?_,hesmall.trans (hdsmall.trans hbsmall),hec⟩
  · rw [hei,hdi,hbi]
    simp only [sourcePrefix,List.length_append]
    omega
  · rw [hef _ (by decide)]
    exact hdlen
  · rw [heram]
    exact hdram
  · rw [herc]
    exact hdrc
  · exact ⟨by rw [heram];exact hddata.originalCall,
      by rw [heram];exact hddata.scalarFields,
      by rw [heram];exact hddata.witnessBits⟩

end NearQuarticWires.StagePrint.Carrier
