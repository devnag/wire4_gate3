import Proof.Quartic.StageCertificateControl.PreparedInput
import Proof.Quartic.StageCertTests.ScheduleFields

/-!
# The whole bitmap fold from a literal prepared source

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageRecovery (countVar widthVar)

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
read the literal original preparation, fetch its actual live dimension,
compute both real bitmap censuses, read the actual counted-pool
header, and perform all signed tests before the sole final crop. -/
def preparedFold : St VV MM :=
  .seq readPreparedInput
    (.seq (StageCertTests.selectParameter 6 (StageCertTests.ScheduleField.variable .k))
      (.seq setBitmapCensuses
        (.seq (StageRecovery.readVariable testCountVar)
          (foldAndCrop firstFlagStore secondFlagStore))))

/-- The complete prepared-source clock of `prop:time`,
paper/paper.tex, includes every scalar field scan,
native flag write, test read, and final prefix operation. -/
def preparedFoldCost (c : Call) (p : Cells.Parameters) (B : ℕ)
    (witness : List Bool) (tests : List NativeTest) : ℕ :=
  preparedInputCost c p B witness+
    (150+(100*(c.n+1)+
      ((30*natBitLength tests.length+32)+(testFoldCost tests+21*paddedCount c.n p.k+24)+1)+1)+1)+1

/-- The literal prepared-source implementation of `sec:algorithm`
and `prop:time`, paper/paper.tex,
constructs the complete flags itself and uses all signed table entries.
Its native and original-center counts are computed from encoded
arity and the actual public parameter record. -/
theorem preparedFold_spec (C : Ctx) (c : Call) (p : Cells.Parameters) (B : ℕ)
    (witness : List Bool) (tests : List NativeTest) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=true::(callWord c++Program.parametersWord p++frame witness++
      natWord tests.length++nativeTestStream tests++rest))
    (hcall : (callWord c).length+2≤C.Wd)
    (hfields : ∀ value∈StageLift.parameterHeadFields p++p.primes.sort (·≤·)++
      StageLift.parameterTailFields p++p.factors,natBitLength value≤B)
    (hB : B+2≤C.Wd) (hcounts : p.primes.card<2^C.Wd ∧ p.factors.length<2^C.Wd)
    (hempty : ∀ store,a.ram store=[] ∧ a.rc store=0)
    (hkn : p.k≤c.n) (hnwidth : c.n+2≤C.Wd)
    (htests : ∀ test∈tests,test.values.length=paddedCount c.n p.k)
    (hTword : natBitLength tests.length+2≤C.Wd) (hTfit : tests.length<2^C.Wd)
    (hvalues : ∀ test∈tests,∀ z∈test.values,encS z<2^test.width)
    (hwidth : ∀ test∈tests,test.width+2≤C.Wd)
    (hboundWord : ∀ test∈tests,natBitLength test.bound+2≤C.Wd)
    (hwidthWord : ∀ test∈tests,natBitLength test.width+2≤C.Wd) :
    Hs C preparedFold a (preparedFoldCost c p B witness tests) (fun b =>
      b.out=a.out++frame ((nativeTestFlags tests (List.replicate (paddedCount c.n p.k) true)).take
        (centerCount c.n p.k))) := by
  have hsmall : C.Wd<2^C.Wd := Nat.lt_two_pow_self
  have hfour : 4≤2^C.Wd := by
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 2≤C.Wd by omega)
    exact hp
  have hNfit : paddedCount c.n p.k<2^C.Wd :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hkeep : centerCount c.n p.k≤paddedCount c.n p.k :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold preparedFold preparedFoldCost
  refine Hs.seq
    (readPreparedInput_spec C c p B witness (natWord tests.length++nativeTestStream tests++rest)
      a hc (by simpa only [List.append_assoc] using hin) hcall hfields hB hcounts hempty)
    fun b ⟨hbn,hbp,hbpc,hbfirst,hbfirstc,hbsecond,hbsecondc,hbi,hbt,hbs,hbc⟩ => ?_
  obtain ⟨d,td,ed,hd,⟨hdk,hdpc,hdr,hds,hdfr⟩⟩ :=
    StageCertTests.selectScheduleField_spec C b p .k hbp (by omega)
  have hda : d.ram firstFlagStore=b.ram firstFlagStore ∧ d.rc firstFlagStore=b.rc firstFlagStore :=
    StageLift.avoidsStore_spec ed (by
      simp [StageLift.avoidsStore,StageLift.avoidsStoreOp,StageCertTests.selectParameter,
        StageCertTests.skipParameterRecords,StageCertTests.ScheduleField.index,StageCertTests.ScheduleField.variable,
        firstFlagStore,StageLift.parameterStore,skipS])
  have hdb : d.ram secondFlagStore=b.ram secondFlagStore ∧ d.rc secondFlagStore=b.rc secondFlagStore :=
    StageLift.avoidsStore_spec ed (by
      simp [StageLift.avoidsStore,StageLift.avoidsStoreOp,StageCertTests.selectParameter,
        StageCertTests.skipParameterRecords,StageCertTests.ScheduleField.index,StageCertTests.ScheduleField.variable,
        secondFlagStore,StageLift.parameterStore,skipS])
  have hdc : Cst d := Cst.of_fr hbc hdfr (by decide)
  have hdn : d.env widthVar=c.n := (hdfr _ (by decide)).trans hbn
  have hdi : d.ip=b.ip := congrArg Prod.fst hds
  refine Hs.seq (show Hs C (StageCertTests.selectParameter 6 (StageCertTests.ScheduleField.variable .k))
    b 150 (·=d) from ⟨d,td,ed,hd,rfl⟩) fun e he => ?_
  subst e
  refine Hs.seq (setBitmapCensuses_spec C d hdc c.n p.k hdn hdk hkn hnwidth)
    fun e ⟨hen,hek,hes,hec,hefr⟩ => ?_
  have hsame := Same.of_sh hes
  have hein : C.inp.drop e.ip=natWord tests.length++(nativeTestStream tests++rest) := by
    rw [hsame.ip,hdi,hbt]
    simp only [List.append_assoc]
  refine Hs.seq
    (StageRecovery.readVariable_spec C e hec testCountVar (by decide) (by decide)
      tests.length _ hein hTword)
    fun f ⟨hfT,hfi,hfr,hfc,hffr⟩ => ?_
  have hfram : f.ram=d.ram := (congrArg (fun q => q.2.1) hfr).trans hsame.ram
  have hfrc : f.rc=d.rc := (congrArg (fun q => q.2.2.1) hfr).trans hsame.rc
  have hfin : C.inp.drop f.ip=nativeTestStream tests++rest := by
    rw [hfi,←List.drop_drop,hein,List.drop_left]
  refine (foldAndCrop_spec C f hfc firstFlagStore secondFlagStore (by decide)
    tests (paddedCount c.n p.k) (centerCount c.n p.k) rest htests hfin
    ((hffr _ (by decide)).trans hen) hNfit hfT hTfit ((hffr _ (by decide)).trans hek) hkeep
    hvalues hwidth hboundWord hwidthWord hfour
    (by rw [hfram,hda.1,hbfirst]) (by rw [hfram,hdb.1,hbsecond])
    (by rw [hfrc,hda.2,hbfirstc]) (by rw [hfrc,hdb.2,hbsecondc])).mono le_rfl ?_
  rintro g hgo
  have hfo : f.out=e.out := congrArg Prod.fst hfr
  have hdo : d.out=b.out := congrArg (fun q => q.2.1) hds
  have hbo : b.out=a.out := congrArg Prod.fst hbs
  rw [hgo,hfo,hsame.out,hdo,hbo]

end NearQuarticWires.StageCertificateControl
