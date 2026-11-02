import Proof.Quartic.StageCertificateControl.InputMergeRound
import Proof.Quartic.StageRecovery.PacketFields

/-!
# Literal test headers and the complete signed table

Paper: the strict tests `eq:testX`–`eq:testPhi`, paper/paper.tex, and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open StageRecovery (countVar widthVar magnitudeVar signVar readVariable)
open StageCertTests (flagVar thresholdVar signedStream updatedFlagList)

/-- A whole test of `sec:algorithm`, paper/paper.tex,
retains its actual strict threshold, record width, and signed native values. -/
structure NativeTest where
  bound : ℕ
  width : ℕ
  values : List ℤ

/-- The exact table input of `lem:print`, paper/paper.tex, is preceded by the two physically serialized scalar headers. -/
def NativeTest.word (test : NativeTest) : List Bool :=
  natWord test.bound++natWord test.width++signedStream test.width test.values

/-- The full encoded census of `lem:print`, paper/paper.tex, includes its terminal table delimiter. -/
theorem NativeTest.word_length (test : NativeTest) :
    test.word.length=(natWord test.bound).length+(natWord test.width).length+
      test.values.length*(2*test.width+1)+1 := by
  have hf := NearCubicGates.Close.WordPrograms.flatMap_frame_length test.width
    (test.values.map fun z => NearCubicWires.RepairOrdinary.SignedSortKey.binary test.width (encS z))
    (by intro w hw;obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw;simp)
  simp only [NativeTest.word,signedStream,NearCubicGates.Close.WordPrograms.recStream,
    List.length_append,List.length_singleton,List.length_map] at hf ⊢
  omega

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
parse the literal threshold and width, then merge one entire table. -/
def inputTest (inputStore outputStore : Fin MM) : St VV MM :=
  .seq (readVariable thresholdVar)
    (.seq (readVariable widthVar) (inputMergeRound inputStore outputStore))

/-- The exact source clock of one test in `prop:time`,
paper/paper.tex, includes both scalar header scans
and all signed records and store rewinds. -/
def NativeTest.sourceCost (test : NativeTest) : ℕ :=
  30*natBitLength test.bound+30*natBitLength test.width+
    test.values.length*(12*test.width+38)+76

/-- The literal whole-test machine of `sec:algorithm` and `prop:time`,
paper/paper.tex, reads both
headers from the source, preserves the following tests, and conjoins
all signed native columns without changing any other store. -/
theorem inputTest_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore≠outputStore)
    (test : NativeTest) (flags : List Bool) (rest : List Bool)
    (hl : flags.length=test.values.length)
    (hin : C.inp.drop a.ip=test.word++rest)
    (hcount : a.env countVar=test.values.length) (hcountfit : test.values.length<2^C.Wd)
    (hvalues : ∀ z∈test.values, encS z<2^test.width)
    (hwidth : test.width+2≤C.Wd)
    (hboundWord : natBitLength test.bound+2≤C.Wd)
    (hwidthWord : natBitLength test.width+2≤C.Wd)
    (hfour : 4≤2^C.Wd)
    (hflags : a.ram inputStore=flags.map Bool.toNat)
    (houtput : (a.ram outputStore).length=test.values.length)
    (hri : a.rc inputStore=test.values.length) (hro : a.rc outputStore=test.values.length) :
    Hs C (inputTest inputStore outputStore) a test.sourceCost (fun b =>
      b.ram=Function.update a.ram outputStore
        ((updatedFlagList test.bound flags test.values).map Bool.toNat) ∧
      b.rc=a.rc ∧ b.ip=a.ip+test.word.length ∧ C.inp.drop b.ip=rest ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b ([thresholdVar,widthVar,c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]++rdNatT)) := by
  unfold inputTest
  refine (Hs.seq (t2 := 30*natBitLength test.width+32+
      (test.values.length*(12*test.width+38)+10)+1)
    (StageRecovery.readVariable_spec C a hc thresholdVar (by decide) (by decide)
      test.bound _ (by simpa only [NativeTest.word,List.append_assoc] using hin) hboundWord)
    fun b ⟨hbb,hbi,hbr,hbc,hbf⟩ => ?_).mono
      (by unfold NativeTest.sourceCost;omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip=natWord test.width++signedStream test.width test.values++rest := by
    rw [hbi,←List.drop_drop,hin]
    simp only [NativeTest.word,List.append_assoc,List.drop_left]
  refine Hs.seq
    (StageRecovery.readVariable_spec C b hbc widthVar (by decide) (by decide)
      test.width _ (by simpa only [List.append_assoc] using hbin) hwidthWord)
    fun d ⟨hdw,hdi,hdr,hdc,hdf⟩ => ?_
  have hdin : C.inp.drop d.ip=signedStream test.width test.values++rest := by
    rw [hdi,←List.drop_drop,hbin]
    simp only [List.append_assoc,List.drop_left]
  have hbram : b.ram=a.ram := congrArg (fun q => q.2.1) hbr
  have hbrc : b.rc=a.rc := congrArg (fun q => q.2.2.1) hbr
  have hdram : d.ram=a.ram := (congrArg (fun q => q.2.1) hdr).trans hbram
  have hdrc : d.rc=a.rc := (congrArg (fun q => q.2.2.1) hdr).trans hbrc
  refine (inputMergeRound_spec C d hdc inputStore outputStore hstores test.width test.bound
    flags test.values rest hl hdin
    (by rw [hdf _ (by decide),hbf _ (by decide),hcount]) hcountfit hvalues hwidth
    ((hdf _ (by decide)).trans hbb) hfour
    (by rw [hdram];exact hflags) (by rw [hdram];exact houtput)
    (by rw [hdrc];exact hri) (by rw [hdrc];exact hro)).mono le_rfl ?_
  rintro e ⟨her,hec,hei,hein,hes,hez,hef⟩
  refine ⟨by rw [her,hdram],hec.trans hdrc,?_,hein,?_,hez,?_⟩
  · rw [hei,hdi,hbi,NativeTest.word_length]
    omega
  · have hds := congrArg (fun q => (q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) hdr
    have hbs := congrArg (fun q => (q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) hbr
    exact hes.trans (hds.trans hbs)
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))

end NearQuarticWires.StageCertificateControl
