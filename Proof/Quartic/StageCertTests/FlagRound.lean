import Proof.Quartic.StageCertTests.FlagList

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageRecovery (countVar)

/-- `sec:algorithm`, paper/paper.tex:
the actual Boolean conjunction array after one whole test table. -/
noncomputable def updatedFlagList (bound : ℕ) (flags : List Bool) (values : List ℤ) : List Bool :=
  List.zipWith (fun flag z => flag && decide (z < (bound:ℤ))) flags values

/-- `sec:algorithm`, paper/paper.tex:
every numeric stored result is the exact encoding of the next
Boolean conjunction array, so subsequent rounds require no new invariant. -/
theorem mergedFlags_as_bool (bound : ℕ) (flags : List Bool) (values : List ℤ) :
    mergedFlags bound flags values = (updatedFlagList bound flags values).map Bool.toNat := by
  rw [updatedFlagList,List.map_zipWith]
  rfl

/-- `sec:algorithm`, paper/paper.tex:
the Boolean conjunction array retains the exact native census. -/
theorem updatedFlagList_length (bound : ℕ) (flags : List Bool) (values : List ℤ)
    (hl : flags.length = values.length) :
    (updatedFlagList bound flags values).length = values.length := by
  simp only [updatedFlagList,List.length_zipWith,hl,Nat.min_self]

/-- `sec:algorithm`, paper/paper.tex:
both retained sequential flag stores are rewound before the next
whole native moment table is merged. -/
def nativeFlagRound (inputStore outputStore : Fin MM) : St VV MM :=
  .seq (.op (.rwM inputStore))
    (.seq (.op (.rwM outputStore)) (nativeFlagList inputStore outputStore))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: a complete native test round pays both full-store
rewinds and the exact signed merge, remaining linear in column count. -/
theorem nativeFlagRound_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore ≠ outputStore)
    (width bound : ℕ) (flags : List Bool) (values : List ℤ)
    (hl : flags.length = values.length)
    (hin : a.kout.drop a.kc = signedStream width values)
    (hcount : a.env countVar = values.length) (hcountfit : values.length < 2 ^ C.Wd)
    (hvalues : ∀ z ∈ values, encS z < 2 ^ width) (hwidth : width < C.Wd)
    (hb : a.env thresholdVar = bound) (hfour : 4 ≤ 2 ^ C.Wd)
    (hflags : a.ram inputStore = flags.map Bool.toNat)
    (houtput : (a.ram outputStore).length = values.length)
    (hri : a.rc inputStore = values.length) (hro : a.rc outputStore = values.length) :
    Hs C (nativeFlagRound inputStore outputStore) a
      (values.length*(10*width+31)+8) (fun b =>
        b.ram outputStore = (updatedFlagList bound flags values).map Bool.toNat ∧
        b.ram inputStore = a.ram inputStore ∧ b.rc inputStore = values.length ∧
        b.rc outputStore = values.length ∧ b.kc = a.kc+values.length*(2*width+1) ∧
        (b.ip,b.out,b.kin,b.kout) = (a.ip,a.out,a.kin,a.kout) ∧ Cst b) := by
  unfold nativeFlagRound
  have hfirst : Hs C (.op (.rwM inputStore)) a (values.length+1) (· = a.rew inputStore) := by
    simpa only [hri] using hs_rwM C inputStore a
  refine (Hs.seq (t2 := values.length+1+(values.length*(10*width+29)+4)+1)
    hfirst fun b hb' => ?_).mono (by ring_nf;omega) (fun _ h => h)
  subst b
  have hnext : (a.rew inputStore).rc outputStore = values.length := by
    simp only [DS.rew,Function.update_of_ne (Ne.symm hstores),hro]
  have hsecond : Hs C (.op (.rwM outputStore)) (a.rew inputStore) (values.length+1)
      (· = (a.rew inputStore).rew outputStore) := by
    simpa only [hnext] using hs_rwM C outputStore (a.rew inputStore)
  refine Hs.seq hsecond fun b hb' => ?_
  subst b
  let start := (a.rew inputStore).rew outputStore
  have hstart : Cst start := ⟨hc.z,hc.one,hc.two⟩
  have hsi : start.rc inputStore = 0 := by simp [start,DS.rew,hstores]
  have hso : start.rc outputStore = 0 := by simp [start,DS.rew]
  refine (nativeFlagList_spec C start hstart inputStore outputStore hstores width bound flags values
    hl hin hcount hcountfit hvalues hwidth hb hfour hflags houtput hsi hso).mono le_rfl ?_
  rintro b ⟨hbo,hbi,hbri,hbro,hbk,hbs,hbc⟩
  exact ⟨by rw [hbo,mergedFlags_as_bool],hbi,hbri,hbro,hbk,hbs,hbc⟩

end NearQuarticWires.StageCertTests
