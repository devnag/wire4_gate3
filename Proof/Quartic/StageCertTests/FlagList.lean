import Proof.Quartic.StageCertTests.FlagEntry
import Proof.Quartic.StageCertTests.SignedList
import Proof.Gates.Cells.Blk

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageRecovery (countVar)

/-- `sec:algorithm`, paper/paper.tex:
the exact numeric conjunction flags after one complete signed moment table. -/
noncomputable def mergedFlags (bound : ℕ) (flags : List Bool) (values : List ℤ) : List ℕ :=
  List.zipWith (fun flag z => (flag && decide (z < (bound:ℤ))).toNat) flags values

/-- `sec:algorithm`, paper/paper.tex:
matched native table and flag censuses are retained by conjunction. -/
theorem mergedFlags_length (bound : ℕ) (flags : List Bool) (values : List ℤ)
    (hl : flags.length = values.length) : (mergedFlags bound flags values).length = values.length := by
  simp only [mergedFlags,List.length_zipWith,hl,Nat.min_self]

/-- `sec:algorithm`, paper/paper.tex:
the physical table merge performs one sequential read and write
for each actual native column position. -/
def nativeFlagList (inputStore outputStore : Fin MM) : St VV MM :=
  forS c0 countVar (nativeFlagEntry inputStore outputStore)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: a full signed native table is conjoined with the
existing flags in linear source time, without a table transpose. -/
theorem nativeFlagList_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore ≠ outputStore)
    (width bound : ℕ) (flags : List Bool) (values : List ℤ)
    (hl : flags.length = values.length)
    (hin : a.kout.drop a.kc = signedStream width values)
    (hcount : a.env countVar = values.length) (hcountfit : values.length < 2 ^ C.Wd)
    (hvalues : ∀ z ∈ values, encS z < 2 ^ width) (hwidth : width < C.Wd)
    (hb : a.env thresholdVar = bound) (hfour : 4 ≤ 2 ^ C.Wd)
    (hflags : a.ram inputStore = flags.map Bool.toNat)
    (houtput : (a.ram outputStore).length = values.length)
    (hri : a.rc inputStore = 0) (hro : a.rc outputStore = 0) :
    Hs C (nativeFlagList inputStore outputStore) a
      (values.length*(10*width+29)+4) (fun b =>
        b.ram outputStore = mergedFlags bound flags values ∧
        b.ram inputStore = a.ram inputStore ∧ b.rc inputStore = values.length ∧
        b.rc outputStore = values.length ∧ b.kc = a.kc+values.length*(2*width+1) ∧
        (b.ip,b.out,b.kin,b.kout) = (a.ip,a.out,a.kin,a.kout) ∧ Cst b) := by
  let result := mergedFlags bound flags values
  have hlen : result.length = values.length := mergedFlags_length bound flags values hl
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ram outputStore = result.take k ++ (a.ram outputStore).drop k ∧
    b.ram inputStore = a.ram inputStore ∧ b.rc inputStore = k ∧ b.rc outputStore = k ∧
    b.kc = a.kc+k*(2*width+1) ∧
    (b.ip,b.out,b.kin,b.kout) = (a.ip,a.out,a.kin,a.kout) ∧
    b.env thresholdVar = bound ∧ Cst b
  unfold nativeFlagList
  refine (forS_spec' c0 countVar (by decide) (nativeFlagEntry inputStore outputStore)
    a values.length hcountfit I (10*width+25)
    (fun k b v ⟨hbo,hbi,hbri,hbro,hbk,hbs,hbb,hbc⟩ => ?_)
    ⟨by simp, rfl,hri,hro,by simp, rfl,hb,hc⟩ hcount ?_).mono le_rfl ?_
  · exact ⟨hbo,hbi,hbri,hbro,hbk,hbs,
      by simpa (config := {decide := true}) [DS.set] using hbb,
      Cst.of_fr (T := [c0]) hbc (Fr.set _ _ (by decide)) (by decide)⟩
  · intro k hk b ⟨hbo,hbi,hbri,hbro,hbk,hbs,hbb,hbc⟩ hbctr hbn
    have hkf : k < flags.length := by omega
    have hkr : k < result.length := by omega
    have hm : values[k] ∈ values := List.getElem_mem hk
    have hbin : b.kout.drop b.kc =
        frame (NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS values[k])) ++
          signedStream width (values.drop (k+1)) := by
      have hko : b.kout = a.kout := by
        have hh := hbs
        simp only [Prod.mk.injEq] at hh
        exact hh.2.2.2
      rw [hko,hbk,←List.drop_drop,hin,signedStream_drop_head width values k hk]
    have hrd : b.rc inputStore < (b.ram inputStore).length := by
      rw [hbri,hbi,hflags,List.length_map,hl]
      exact hk
    have hwr : b.rc outputStore ≤ (b.ram outputStore).length := by
      rw [hbro,hbo,List.length_append,List.length_take,List.length_drop,hlen,houtput,
        Nat.min_eq_left hk.le]
      omega
    have hflag : (b.ram inputStore).getD (b.rc inputStore) 0 = flags[k].toNat := by
      rw [hbi,hflags,hbri,List.getD_eq_getElem _ _ (by simp;omega),List.getElem_map]
    have hrk : result[k] = (flags[k] && decide (values[k] < (bound:ℤ))).toNat := by
      simp only [result,mergedFlags,List.getElem_zipWith]
    refine (nativeFlagEntry_spec C b hbc inputStore outputStore hstores width values[k] bound flags[k]
      _ hbin (hvalues _ hm) hwidth hbb hfour hrd hwr hflag).mono le_rfl ?_
    rintro d ⟨hdk,hds,hdi,hdo,hdri,hdro,hdc,hdf⟩
    refine ⟨⟨?_,hdi.trans hbi,by rw [hdri,hbri],by rw [hdro,hbro],
      by rw [hdk,hbk];ring,hds.trans hbs,by rw [hdf _ (by decide),hbb],hdc⟩,
      by rw [hdf _ (by decide),hbctr],by rw [hdf _ (by decide),hbn]⟩
    rw [hdo,hbo,hbro,←hrk]
    have htake : (result.take k).length = k := by simp only [List.length_take,Nat.min_eq_left hkr.le]
    have hp := putAt_split (result.take k) ((a.ram outputStore).drop k) result[k]
    rw [htake] at hp
    rw [hp,List.take_succ_eq_append_getElem hkr]
    simp only [List.drop_drop,List.singleton_append,List.append_assoc]
  · rintro b ⟨⟨hbo,hbi,hbri,hbro,hbk,hbs,_,hbc⟩,_,_⟩
    refine ⟨?_,hbi,hbri,hbro,hbk,hbs,hbc⟩
    simpa only [List.take_of_length_le (by omega : result.length ≤ values.length),
      List.drop_of_length_le (by omega : (a.ram outputStore).length ≤ values.length),List.append_nil] using hbo

end NearQuarticWires.StageCertTests
