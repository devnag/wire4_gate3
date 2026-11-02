import Proof.Quartic.StageCertificateControl.InputMergeEntry
import Proof.Quartic.StageCertTests.FlagList

/-!
# Sequential signed tables update the complete bitmap

Paper: `sec:algorithm`, paper/paper.tex,
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
open StageCertTests (flagVar thresholdVar signedStream mergedFlags)

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
one complete signed native table is conjoined with the old bitmap. -/
def inputMergeList (inputStore outputStore : Fin MM) : St VV MM :=
  forS c0 countVar (inputMergeEntry inputStore outputStore)

/-- The whole-table scan of `sec:algorithm` and `prop:time`,
paper/paper.tex, retains every
signed native column, the following input suffix, and all other stores.
Its source clock is linear in the actual column census. -/
theorem inputMergeList_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore≠outputStore)
    (width bound : ℕ) (flags : List Bool) (values : List ℤ) (rest : List Bool)
    (hl : flags.length=values.length)
    (hin : C.inp.drop a.ip=signedStream width values++rest)
    (hcount : a.env countVar=values.length) (hcountfit : values.length<2^C.Wd)
    (hvalues : ∀ z∈values, encS z<2^width) (hwidth : width+2≤C.Wd)
    (hb : a.env thresholdVar=bound) (hfour : 4≤2^C.Wd)
    (hflags : a.ram inputStore=flags.map Bool.toNat)
    (houtput : (a.ram outputStore).length=values.length)
    (hri : a.rc inputStore=0) (hro : a.rc outputStore=0) :
    Hs C (inputMergeList inputStore outputStore) a
      (values.length*(12*width+36)+4) (fun b =>
        b.ram=Function.update a.ram outputStore (mergedFlags bound flags values) ∧
        b.rc=Function.update (Function.update a.rc inputStore values.length)
          outputStore values.length ∧
        b.ip=a.ip+values.length*(2*width+1) ∧
        (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
        Fr a b [c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]) := by
  let result := mergedFlags bound flags values
  have hlen : result.length=values.length := StageCertTests.mergedFlags_length bound flags values hl
  let changed : List (Fin VV) := [c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ram=Function.update a.ram outputStore (result.take k++(a.ram outputStore).drop k) ∧
    b.rc=Function.update (Function.update a.rc inputStore k) outputStore k ∧
    b.ip=a.ip+k*(2*width+1) ∧
    (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧ Fr a b changed
  unfold inputMergeList
  refine (forS_spec' c0 countVar (by decide) (inputMergeEntry inputStore outputStore)
    a values.length hcountfit I (12*width+32)
    (fun k b v ⟨hbr,hbc,hbi,hbs,hcc,hbf⟩ => ?_)
    ⟨by simp,?_,by simp,rfl,hc,Fr.refl _ _⟩ hcount ?_).mono le_rfl ?_
  · exact ⟨hbr,hbc,hbi,hbs,
      Cst.of_fr (T := [c0]) hcc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by simp [changed]))⟩
  · ext m
    by_cases hma : m=inputStore
    · subst m
      simp [hstores,hri]
    · by_cases hmb : m=outputStore
      · subst m
        simp [hro]
      · simp [hma,hmb]
  · intro k hk b ⟨hbr,hbc,hbi,hbs,hcc,hbf⟩ hbctr hbn
    have hkf : k<flags.length := by omega
    have hkr : k<result.length := by omega
    have hba : b.ram inputStore=a.ram inputStore := by
      rw [hbr,Function.update_of_ne hstores]
    have hbb : b.ram outputStore=result.take k++(a.ram outputStore).drop k := by
      rw [hbr,Function.update_self]
    have hbri : b.rc inputStore=k := by simp [hbc,hstores]
    have hbro : b.rc outputStore=k := by simp [hbc]
    have hbin : C.inp.drop b.ip=
        frame (NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS values[k]))++
          (signedStream width (values.drop (k+1))++rest) := by
      rw [hbi,←List.drop_drop,hin,List.drop_append_of_le_length]
      · rw [StageCertTests.signedStream_drop_head width values k hk,List.append_assoc]
      · have hh : k*(2*width+1)≤(signedStream width values).length := by
          unfold signedStream
          rw [NearCubicGates.Close.WordPrograms.recStream,List.length_append]
          have hlenw : ∀ w∈values.map (fun z => NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS z)), w.length=width := by
            intro w hw
            obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw
            simp
          rw [NearCubicGates.Close.WordPrograms.flatMap_frame_length width _ hlenw,List.length_map]
          simpa only [List.length_singleton] using
            (Nat.le_trans (Nat.mul_le_mul_right (2*width+1) hk.le) (Nat.le_add_right _ 1))
        exact hh
    have hrd : b.rc inputStore<(b.ram inputStore).length := by
      rw [hbri,hba,hflags,List.length_map,hl]
      exact hk
    have hwr : b.rc outputStore≤(b.ram outputStore).length := by
      rw [hbro,hbb,List.length_append,List.length_take,List.length_drop,hlen,houtput,
        Nat.min_eq_left hk.le]
      omega
    have hflag : (b.ram inputStore).getD (b.rc inputStore) 0=flags[k].toNat := by
      rw [hba,hflags,hbri,List.getD_eq_getElem _ _ (by simp;omega),List.getElem_map]
    have hrk : result[k]=(flags[k] && decide (values[k]<(bound:ℤ))).toNat := by
      simp only [result,mergedFlags,List.getElem_zipWith]
    refine (inputMergeEntry_spec C b hcc inputStore outputStore hstores width values[k] bound flags[k]
      _ hbin (hvalues _ (List.getElem_mem hk)) hwidth
      ((hbf _ (by decide)).trans hb) hfour hrd hwr hflag).mono le_rfl ?_
    rintro d ⟨hdi,hds,hdr,hdrc,hdc,hdf⟩
    have hnew : Fr a d changed := Fr.trans hbf (Fr.weaken hdf (by decide))
    refine ⟨⟨?_,?_,by rw [hdi,hbi];ring,hds.trans hbs,hdc,hnew⟩,
      by rw [hdf _ (by decide),hbctr],by rw [hdf _ (by decide),hbn]⟩
    · rw [hdr,hbb,hbro,←hrk,hbr,Function.update_idem]
      have htake : (result.take k).length=k := by simp [Nat.min_eq_left hkr.le]
      have hp := putAt_split (result.take k) ((a.ram outputStore).drop k) result[k]
      rw [htake] at hp
      rw [hp,List.take_succ_eq_append_getElem hkr]
      simp only [List.drop_drop,List.singleton_append,List.append_assoc]
    · rw [hdrc,hbri,hbro,hbc]
      simp only [Function.update_comm hstores,Function.update_idem]
  · rintro b ⟨⟨hbr,hbc,hbi,hbs,hcc,hbf⟩,_,_⟩
    refine ⟨?_,hbc,hbi,hbs,hcc,hbf⟩
    simpa only [List.take_of_length_le (by omega : result.length≤values.length),
      List.drop_of_length_le (by omega : (a.ram outputStore).length≤values.length),List.append_nil] using hbr

end NearQuarticWires.StageCertificateControl
