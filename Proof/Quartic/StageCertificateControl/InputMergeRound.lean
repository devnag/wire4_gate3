import Proof.Quartic.StageCertificateControl.InputMergeList
import Proof.Quartic.StageCertTests.FlagRound

/-!
# One complete signed table round

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open StageRecovery (countVar magnitudeVar signVar)
open StageCertTests (flagVar thresholdVar signedStream updatedFlagList)

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
rewind both complete flag arrays, merge the actual input records,
and consume their terminal delimiter before the next table header. -/
def inputMergeRound (inputStore outputStore : Fin MM) : St VV MM :=
  .seq (.op (.rwM inputStore)) (.seq (.op (.rwM outputStore))
    (.seq (inputMergeList inputStore outputStore) (.op (.rdI vJ))))

/-- The signed whole-table round of `sec:algorithm` and `prop:time`,
paper/paper.tex, pays both full
rewinds and the terminal delimiter. Every other store and stream is
unchanged, and the next table suffix is located exactly. -/
theorem inputMergeRound_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore≠outputStore)
    (width bound : ℕ) (flags : List Bool) (values : List ℤ) (rest : List Bool)
    (hl : flags.length=values.length)
    (hin : C.inp.drop a.ip=signedStream width values++rest)
    (hcount : a.env countVar=values.length) (hcountfit : values.length<2^C.Wd)
    (hvalues : ∀ z∈values, encS z<2^width) (hwidth : width+2≤C.Wd)
    (hb : a.env thresholdVar=bound) (hfour : 4≤2^C.Wd)
    (hflags : a.ram inputStore=flags.map Bool.toNat)
    (houtput : (a.ram outputStore).length=values.length)
    (hri : a.rc inputStore=values.length) (hro : a.rc outputStore=values.length) :
    Hs C (inputMergeRound inputStore outputStore) a
      (values.length*(12*width+38)+10) (fun b =>
        b.ram=Function.update a.ram outputStore
          ((updatedFlagList bound flags values).map Bool.toNat) ∧
        b.rc=a.rc ∧ b.ip=a.ip+(values.length*(2*width+1)+1) ∧
        C.inp.drop b.ip=rest ∧
        (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
        Fr a b [c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]) := by
  unfold inputMergeRound
  have hfirst : Hs C (.op (.rwM inputStore)) a (values.length+1)
      (·=a.rew inputStore) := by simpa only [hri] using hs_rwM C inputStore a
  refine (Hs.seq (t2 := values.length+1+(values.length*(12*width+36)+6)+1)
    hfirst fun b hb' => ?_).mono (by ring_nf;omega) (fun _ h => h)
  subst b
  have hsecond : Hs C (.op (.rwM outputStore)) (a.rew inputStore) (values.length+1)
      (·=(a.rew inputStore).rew outputStore) := by
    simpa only [DS.rew,Function.update_of_ne (Ne.symm hstores),hro] using
      hs_rwM C outputStore (a.rew inputStore)
  refine Hs.seq hsecond fun b hb' => ?_
  subst b
  let start := (a.rew inputStore).rew outputStore
  have hstart : Cst start := ⟨hc.z,hc.one,hc.two⟩
  have hsi : start.rc inputStore=0 := by simp [start,DS.rew,hstores]
  have hso : start.rc outputStore=0 := by simp [start,DS.rew]
  refine Hs.seq (t2 := 1)
    (inputMergeList_spec C start hstart inputStore outputStore hstores width bound flags values rest
      hl hin hcount hcountfit hvalues hwidth hb hfour hflags houtput hsi hso)
    fun b ⟨hbr,hbc,hbi,hbs,hcc,hbf⟩ => ?_
  have hflat : ((values.map fun z => NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS z)).flatMap frame).length=
      values.length*(2*width+1) := by
    rw [NearCubicGates.Close.WordPrograms.flatMap_frame_length width _
      (by intro w hw;obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw;simp),List.length_map]
  change b.ip=a.ip+values.length*(2*width+1) at hbi
  have htail : C.inp.drop b.ip=false::rest := by
    rw [hbi,←List.drop_drop,hin]
    change ((values.map fun z => NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS z)).flatMap frame++[false]++rest).drop
      (values.length*(2*width+1))=false::rest
    rw [←hflat,List.append_assoc,List.drop_left]
    rfl
  have hread : b.ip<C.inp.length := by
    have hh := congrArg List.length htail
    simp only [List.length_drop,List.length_cons] at hh
    omega
  refine (hs_rdI C vJ b hread).mono le_rfl ?_
  rintro d rfl
  refine ⟨?_,?_,?_,?_,hbs,?_,?_⟩
  · change b.ram=_
    rw [hbr,StageCertTests.mergedFlags_as_bool]
    rfl
  · change b.rc=_
    rw [hbc]
    ext m
    by_cases hma : m=inputStore
    · subst m
      simp [start,DS.rew,hstores,hri]
    · by_cases hmb : m=outputStore
      · subst m
        simp [hro]
      · simp [start,DS.rew,hma,hmb]
  · change b.ip+1=_
    change b.ip=a.ip+values.length*(2*width+1) at hbi
    omega
  · change C.inp.drop (b.ip+1)=rest
    rw [←List.drop_drop,htail]
    rfl
  · exact Cst.of_fr (T := [vJ]) hcc (Fr.set _ _ (by decide)) (by decide)
  · exact Fr.trans hbf (Fr.set _ _ (by decide))

end NearQuarticWires.StageCertificateControl
