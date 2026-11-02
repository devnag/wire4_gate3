import Proof.Quartic.StageCertTests.FlagInputEntry

/-!
# A native signed input record updates the next flag store

Paper: the strict whole-table tests of `eq:testX`–`eq:testPhi`,
paper/paper.tex, and Step 2 of
`sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open StageRecovery (magnitudeVar signVar)
open StageCertTests (flagVar thresholdVar testNativeFlag)

/-- Step 2 of `sec:algorithm`, paper/paper.tex, reads a real signed table record and an old bitmap
bit, then stores their exact strict conjunction in the next array. -/
def inputMergeEntry (inputStore outputStore : Fin MM) : St VV MM :=
  .seq rdRec (.seq (.op (.copy u4 t3))
    (.seq (.op (.rdM inputStore flagVar))
      (.seq testNativeFlag (.op (.wrM outputStore flagVar)))))

/-- The actual source-input merge in Step 2,
`sec:algorithm`, paper/paper.tex, preserves
signed values on all columns and changes only the two sequential
flag cursors and the destination flag entry. -/
theorem inputMergeEntry_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore≠outputStore)
    (width : ℕ) (z : ℤ) (bound : ℕ) (flag : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip=frame
      (NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS z))++rest)
    (hz : encS z<2^width) (hwidth : width+2 ≤ C.Wd)
    (hb : a.env thresholdVar=bound) (hfour : 4 ≤ 2^C.Wd)
    (hr : a.rc inputStore<(a.ram inputStore).length)
    (hw : a.rc outputStore ≤ (a.ram outputStore).length)
    (hflag : (a.ram inputStore).getD (a.rc inputStore) 0=flag.toNat) :
    Hs C (inputMergeEntry inputStore outputStore) a (12*width+32) (fun b =>
      b.ip=a.ip+(2*width+1) ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧
      b.ram=Function.update a.ram outputStore
        (putAt (a.ram outputStore) (a.rc outputStore)
          (flag && decide (z<(bound:ℤ))).toNat) ∧
      b.rc=Function.update (Function.update a.rc inputStore (a.rc inputStore+1))
        outputStore (a.rc outputStore+1) ∧ Cst b ∧
      Fr a b [t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]) := by
  unfold inputMergeEntry
  refine (Hs.seq (t2 := 14) (rdRec_spec a hc width (encS z) rest hin hz hwidth)
    fun b ⟨hbv,hbi,hbr,hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hbrm : b.ram=a.ram := congrArg (fun q => q.2.1) hbr
  have hbrc : b.rc=a.rc := congrArg (fun q => q.2.2.1) hbr
  refine Hs.seq (t2 := 12) (hs_copy C u4 t3 b (by decide)) fun d hd => ?_
  subst d
  let d := b.set u4 (b.env t3)
  have hdc : Cst d := Cst.of_fr (T := [u4]) hbc (Fr.set _ _ (by decide)) (by decide)
  have hrd : d.rc inputStore<(d.ram inputStore).length := by
    change b.rc inputStore<(b.ram inputStore).length
    rw [hbrc,hbrm]
    exact hr
  refine Hs.seq (t2 := 10) (hs_rdM C inputStore flagVar d hrd) fun e he => ?_
  subst e
  let e := (d.set flagVar ((d.ram inputStore).getD (d.rc inputStore) 0)).adv inputStore
  have hec : Cst e := by
    refine ⟨?_,?_,?_⟩ <;> simp (config := {decide := true}) [e,DS.adv,DS.set,hdc.z,hdc.one,hdc.two]
  have heu : e.env u4=encS z := by
    simp (config := {decide := true}) [e,d,DS.adv,DS.set,hbv]
  have heb : e.env thresholdVar=bound := by
    have hh : b.env thresholdVar=bound := (hbf _ (by decide)).trans hb
    simp (config := {decide := true}) [e,d,DS.adv,DS.set,hh]
  have hef : e.env flagVar=flag.toNat := by
    simp only [e,DS.adv,DS.set_env_self]
    change (b.ram inputStore).getD (b.rc inputStore) 0=_
    rw [hbrm,hbrc,hflag]
  refine Hs.seq (t2 := 1)
    (StageCertTests.testNativeFlag_spec C e hec z bound flag heu heb hef hfour)
    fun f ⟨hff,hfs,hfr⟩ => ?_
  have hfm := Same.of_sh hfs
  have hfc : Cst f := Cst.of_fr hec hfr (by decide)
  have hfmram : f.ram=a.ram := by rw [hfm.ram];exact hbrm
  have hfmrc : f.rc=Function.update a.rc inputStore (a.rc inputStore+1) := by
    rw [hfm.rc]
    simp only [e,d,DS.adv,DS.set_rc,hbrc]
  have hro : f.rc outputStore=a.rc outputStore := by
    rw [hfmrc,Function.update_of_ne (Ne.symm hstores)]
  refine (hs_wrM C outputStore flagVar f (by rw [hro,hfmram];exact hw)).mono (by omega) ?_
  rintro g rfl
  refine ⟨?_,?_,?_,?_,⟨hfc.z,hfc.one,hfc.two⟩,?_⟩
  · change f.ip=_
    rw [hfm.ip]
    exact hbi
  · change (f.out,f.kin,f.kout,f.kc)=_
    rw [hfm.out,hfm.kin,hfm.kout,hfm.kc]
    exact congrArg (fun q => (q.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) hbr
  · change Function.update f.ram outputStore
      (putAt (f.ram outputStore) (f.rc outputStore) (f.env flagVar))=_
    rw [hro,hff,hfmram]
  · change Function.update f.rc outputStore (f.rc outputStore+1)=_
    rw [hro,hfmrc]
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken hfr (by decide))))

end NearQuarticWires.StageCertificateControl
