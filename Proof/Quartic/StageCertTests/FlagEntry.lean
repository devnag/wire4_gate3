import Proof.Quartic.StageCertTests.FlagArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u3 u4 u5 u9)
open StageRecovery (magnitudeVar signVar)

/-- `sec:algorithm`, paper/paper.tex:
one native table entry updates a sequential flag store. Distinct
input and output stores permit one linear pass through each table. -/
def nativeFlagEntry (inputStore outputStore : Fin MM) : St VV MM :=
  .seq NearCubicGates.Close.CounterMachine.CellTables.rdRec
    (.seq (.op (.rdM inputStore flagVar))
      (.seq testNativeFlag (.op (.wrM outputStore flagVar))))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the actual native-table merge reads one old flag,
applies the signed strict test and writes one new flag, preserving
the complete original call and the native table stream. -/
theorem nativeFlagEntry_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputStore outputStore : Fin MM) (hstores : inputStore ≠ outputStore)
    (width : ℕ) (z : ℤ) (bound : ℕ) (flag : Bool) (rest : List Bool)
    (hin : a.kout.drop a.kc = frame
      (NearCubicWires.RepairOrdinary.SignedSortKey.binary width (encS z)) ++ rest)
    (hz : encS z < 2 ^ width) (hwidth : width < C.Wd)
    (hb : a.env thresholdVar = bound) (hfour : 4 ≤ 2 ^ C.Wd)
    (hr : a.rc inputStore < (a.ram inputStore).length)
    (hw : a.rc outputStore ≤ (a.ram outputStore).length)
    (hflag : (a.ram inputStore).getD (a.rc inputStore) 0 = flag.toNat) :
    Hs C (nativeFlagEntry inputStore outputStore) a (10*width+25) (fun b =>
      b.kc = a.kc+(2*width+1) ∧
      (b.ip,b.out,b.kin,b.kout) = (a.ip,a.out,a.kin,a.kout) ∧
      b.ram inputStore = a.ram inputStore ∧
      b.ram outputStore = putAt (a.ram outputStore) (a.rc outputStore)
        (flag && decide (z < (bound:ℤ))).toNat ∧
      b.rc inputStore = a.rc inputStore+1 ∧ b.rc outputStore = a.rc outputStore+1 ∧
      Cst b ∧ Fr a b [u3,u4,u5,u9,flagVar,magnitudeVar,signVar,vJ]) := by
  unfold nativeFlagEntry
  refine (Hs.seq (t2 := 12)
    (NearCubicGates.Close.CounterMachine.CellTables.rdRec_spec C a hc width (encS z) rest hin hz hwidth)
    fun b ⟨hbv,hbk,hbf,hbs⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hbr : b.rc inputStore < (b.ram inputStore).length := by rw [hbs.rc,hbs.ram];exact hr
  refine Hs.seq (t2 := 10) (hs_rdM C inputStore flagVar b hbr) fun d hd => ?_
  subst d
  let d := (b.set flagVar ((b.ram inputStore).getD (b.rc inputStore) 0)).adv inputStore
  have hdc : Cst d := by
    refine ⟨?_,?_,?_⟩ <;> simp (config := {decide := true}) [d,DS.adv,DS.set,hbc.z,hbc.one,hbc.two]
  have hdu : d.env u4 = encS z := by simp (config := {decide := true}) [d,DS.adv,DS.set,hbv]
  have hdb : d.env thresholdVar = bound := by
    have hh : b.env thresholdVar = bound := by rw [hbf _ (by decide),hb]
    simp (config := {decide := true}) [d,DS.adv,DS.set,hh]
  have hdf : d.env flagVar = flag.toNat := by
    simp only [d,DS.adv,DS.set_env_self]
    rw [hbs.ram,hbs.rc,hflag]
  refine Hs.seq (t2 := 1) (testNativeFlag_spec C d hdc z bound flag hdu hdb hdf hfour)
    fun e ⟨hef,hes,her⟩ => ?_
  have hem := Same.of_sh hes
  have hec : Cst e := Cst.of_fr hdc her (by decide)
  have heOut : e.ram outputStore = a.ram outputStore := by rw [hem.ram];exact congrFun hbs.ram _
  have heIn : e.ram inputStore = a.ram inputStore := by rw [hem.ram];exact congrFun hbs.ram _
  have heRi : e.rc inputStore = a.rc inputStore+1 := by
    rw [hem.rc]
    simp [d,DS.adv,hbs.rc]
  have heRo : e.rc outputStore = a.rc outputStore := by
    rw [hem.rc]
    simp only [d,DS.adv,DS.set_rc,Function.update_of_ne (Ne.symm hstores)]
    exact congrFun hbs.rc _
  have hew : e.rc outputStore ≤ (e.ram outputStore).length := by rw [heRo,heOut];exact hw
  refine (hs_wrM C outputStore flagVar e hew).mono le_rfl ?_
  rintro f rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change e.kc = _
    rw [hem.kc]
    exact hbk
  · change (e.ip,e.out,e.kin,e.kout) = _
    rw [hem.ip,hem.out,hem.kin,hem.kout]
    simp only [Prod.mk.injEq]
    exact ⟨hbs.ip,hbs.out,hbs.kin,hbs.kout⟩
  · simp only [DS.put,Function.update_of_ne hstores]
    exact heIn
  · simp only [DS.put,Function.update_self]
    rw [heOut,heRo,hef]
  · simp only [DS.put,Function.update_of_ne hstores]
    exact heRi
  · simp only [DS.put,Function.update_self]
    rw [heRo]
  · exact ⟨hec.z,hec.one,hec.two⟩
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken her (by decide)))

end NearQuarticWires.StageCertTests
