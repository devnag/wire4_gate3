import Proof.Quartic.StageCertificateControl.AlternatingTest

/-!
# A counted fold of every complete signed test

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and the time bound `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open StageRecovery (countVar widthVar magnitudeVar signVar)
open StageCertTests (flagVar thresholdVar updatedFlagList)

/-- The test counter of `sec:algorithm`, paper/paper.tex, is distinct from the inner native-column counter. -/
def testIndexVar : Fin VV := ⟨120,by decide⟩

/-- The full test census of `sec:algorithm`, paper/paper.tex, is retained while each native table is scanned. -/
def testCountVar : Fin VV := ⟨121,by decide⟩

/-- The actual test stream of `sec:algorithm`, paper/paper.tex, concatenates complete threshold/width/table packets. -/
def nativeTestStream (tests : List NativeTest) : List Bool := tests.flatMap NativeTest.word

/-- The whole signed conjunction of `sec:algorithm`, paper/paper.tex, retains every native position through the last test. -/
noncomputable def nativeTestFlags (tests : List NativeTest) (flags : List Bool) : List Bool :=
  tests.foldl (fun flags test => updatedFlagList test.bound flags test.values) flags

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
matched whole-table censuses preserve the complete bitmap length. -/
theorem nativeTestFlags_length (tests : List NativeTest) (flags : List Bool) (count : ℕ)
    (htests : ∀ test∈tests, test.values.length=count) (hflags : flags.length=count) :
    (nativeTestFlags tests flags).length=count := by
  induction tests generalizing flags with
  | nil => exact hflags
  | cons test tests ih =>
    apply ih (updatedFlagList test.bound flags test.values) (fun t ht => htests t (by simp [ht]))
    exact (StageCertTests.updatedFlagList_length test.bound flags test.values
      (hflags.trans (htests test (by simp)).symm)).trans (htests test (by simp))

/-- The original whole-table loop of `sec:algorithm`,
paper/paper.tex, uses the two complete retained arrays. -/
def testFold (first second : Fin MM) : St VV MM :=
  forS testIndexVar testCountVar (alternatingTest first second)

/-- The explicit source budget of `prop:time`, paper/paper.tex, charges every test and every counted-loop operation.
The harmless extra test-census factor remains polynomial. -/
def testFoldCost (tests : List NativeTest) : ℕ :=
  tests.length*((tests.map NativeTest.sourceCost).sum+7)+4

/-- The counted whole-test loop of `sec:algorithm` and `prop:time`,
paper/paper.tex, performs the
complete signed conjunction. It preserves every other store, retains
the whole native bitmap, and consumes exactly the actual test stream. -/
theorem testFold_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (first second : Fin MM) (hstores : first≠second)
    (initialMode : Bool) (hmode : a.env modeVar=initialMode.toNat)
    (tests : List NativeTest) (flags : List Bool) (count : ℕ) (rest : List Bool)
    (htests : ∀ test∈tests, test.values.length=count) (hflagsLength : flags.length=count)
    (hin : C.inp.drop a.ip=nativeTestStream tests++rest)
    (hn : a.env countVar=count) (hnfit : count<2^C.Wd)
    (htestCount : a.env testCountVar=tests.length) (htestFit : tests.length<2^C.Wd)
    (hvalues : ∀ test∈tests, ∀ z∈test.values, encS z<2^test.width)
    (hwidth : ∀ test∈tests, test.width+2≤C.Wd)
    (hboundWord : ∀ test∈tests, natBitLength test.bound+2≤C.Wd)
    (hwidthWord : ∀ test∈tests, natBitLength test.width+2≤C.Wd) (hfour : 4≤2^C.Wd)
    (hflags : a.ram (activeStore first second initialMode)=flags.map Bool.toNat)
    (hother : (a.ram (activeStore first second (!initialMode))).length=count)
    (hri : a.rc first=count) (hro : a.rc second=count) :
    Hs C (testFold first second) a (testFoldCost tests) (fun b =>
      ∃ mode : Bool, b.env modeVar=mode.toNat ∧
        b.ram (activeStore first second mode)=(nativeTestFlags tests flags).map Bool.toNat ∧
        (b.ram (activeStore first second (!mode))).length=count ∧
        b.rc=a.rc ∧ (∀ store,store≠first→store≠second→b.ram store=a.ram store) ∧
        b.ip=a.ip+(nativeTestStream tests).length ∧ C.inp.drop b.ip=rest ∧
        (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
        Fr a b (testIndexVar::modeVar::([thresholdVar,widthVar,c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]++rdNatT))) := by
  let changed : List (Fin VV) := testIndexVar::modeVar::
    ([thresholdVar,widthVar,c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]++rdNatT)
  let I : ℕ → DS VV MM → Prop := fun k b =>
    ∃ mode : Bool, b.env modeVar=mode.toNat ∧
      b.ram (activeStore first second mode)=(nativeTestFlags (tests.take k) flags).map Bool.toNat ∧
      (b.ram (activeStore first second (!mode))).length=count ∧
      b.rc=a.rc ∧ (∀ store,store≠first→store≠second→b.ram store=a.ram store) ∧
      b.ip=a.ip+(nativeTestStream (tests.take k)).length ∧
      C.inp.drop b.ip=nativeTestStream (tests.drop k)++rest ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧ Fr a b changed
  have hcost : ∀ test∈tests, test.sourceCost≤(tests.map NativeTest.sourceCost).sum := by
    intro test ht
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨test,ht,rfl⟩)
  unfold testFold testFoldCost
  refine (forS_spec' testIndexVar testCountVar (by decide) (alternatingTest first second)
    a tests.length htestFit I ((tests.map NativeTest.sourceCost).sum+3)
    (fun k b v ⟨mode,hm,hf,ho,hr,hotherStores,hi,ht,hs,hcc,hfr⟩ => ?_)
    ⟨initialMode,hmode,by simpa [nativeTestFlags] using hflags,hother,rfl,
      by intro store _ _;rfl,by simp [nativeTestStream],by simpa [nativeTestStream] using hin,
      rfl,hc,Fr.refl _ _⟩ htestCount ?_).mono (by simp only [Nat.add_assoc,Nat.reduceAdd];exact le_rfl) ?_
  · refine ⟨mode,?_,hf,ho,hr,hotherStores,hi,ht,hs,?_,?_⟩
    · simpa only [DS.set_env_ne _ _ (by decide : modeVar≠testIndexVar)] using hm
    · exact Cst.of_fr (T := [testIndexVar]) hcc (Fr.set _ _ (by decide)) (by decide)
    · exact Fr.trans hfr (Fr.set _ _ (by simp [changed]))
  · intro k hk b ⟨mode,hm,hf,ho,hr,hotherStores,hi,ht,hs,hcc,hfr⟩ hbidx hbcount
    have hmem : tests[k]∈tests := List.getElem_mem hk
    have hlen : (nativeTestFlags (tests.take k) flags).length=tests[k].values.length := by
      rw [htests _ hmem]
      exact nativeTestFlags_length _ flags count
        (fun test hm => htests test (List.mem_of_mem_take hm)) hflagsLength
    have hinput : C.inp.drop b.ip=tests[k].word++(nativeTestStream (tests.drop (k+1))++rest) := by
      rw [ht,List.drop_eq_getElem_cons hk]
      simp only [nativeTestStream,List.flatMap_cons,List.append_assoc]
    have hnext : nativeTestFlags (tests.take (k+1)) flags=
        updatedFlagList tests[k].bound (nativeTestFlags (tests.take k) flags) tests[k].values := by
      rw [List.take_succ_eq_append_getElem hk]
      simp only [nativeTestFlags,List.foldl_append,List.foldl_cons,List.foldl_nil]
    refine (alternatingTest_spec C b hcc first second hstores mode hm tests[k]
      (nativeTestFlags (tests.take k) flags) _ hlen hinput
      (by rw [hfr _ (by decide),hn,htests _ hmem])
      (by rw [htests _ hmem];exact hnfit) (hvalues _ hmem) (hwidth _ hmem)
      (hboundWord _ hmem) (hwidthWord _ hmem) hfour hf
      (by rw [htests _ hmem];exact ho)
      (by rw [hr,hri,htests _ hmem]) (by rw [hr,hro,htests _ hmem])).mono
      (by have hh := hcost _ hmem;omega) ?_
    rintro d ⟨hdm,hdr,hdrc,hdi,hdt,hds,hdc,hdf⟩
    refine ⟨⟨!mode,hdm,?_,?_,hdrc.trans hr,?_,?_,hdt,hds.trans hs,hdc,
      Fr.trans hfr (Fr.weaken hdf (by intro y hy;exact List.mem_cons_of_mem _ hy))⟩,
      by rw [hdf _ (by decide),hbidx],by rw [hdf _ (by decide),hbcount]⟩
    · rw [hdr,Function.update_self,hnext]
    · rw [hdr,Bool.not_not,Function.update_of_ne]
      · rw [hf,List.length_map]
        exact hlen.trans (htests _ hmem)
      · cases mode
        · simpa [activeStore] using hstores
        · simpa [activeStore] using Ne.symm hstores
    · intro store hs1 hs2
      rw [hdr,Function.update_of_ne]
      · exact hotherStores store hs1 hs2
      · cases mode
        · simpa [activeStore] using hs2
        · simpa [activeStore] using hs1
    · rw [hdi,hi,List.take_succ_eq_append_getElem hk]
      simp only [nativeTestStream,List.flatMap_append,List.flatMap_singleton,List.length_append]
      omega
  · rintro b ⟨⟨mode,hm,hf,ho,hr,hotherStores,hi,ht,hs,hcc,hfr⟩,_,_⟩
    refine ⟨mode,hm,?_,ho,hr,hotherStores,?_,?_,hs,hcc,hfr⟩
    · simpa only [List.take_length] using hf
    · simpa only [List.take_length] using hi
    · simpa only [List.drop_length,nativeTestStream,List.flatMap_nil,List.nil_append] using ht

end NearQuarticWires.StageCertificateControl
