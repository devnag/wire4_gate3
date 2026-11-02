import Proof.Quartic.StageCertTests.FlagOutput
import Proof.Quartic.StageCertTests.SignedList

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open StageRecovery (magnitudeVar signVar)

/-- `sec:algorithm`, paper/paper.tex:
one signed native input record and one retained bit produce one
framed conjunction bit without retaining a second table. -/
def inputFlagEntry (store : Fin MM) : St VV MM :=
  .seq rdRec (.seq (.op (.copy u4 t3))
    (.seq (.op (.rdM store flagVar)) (.seq testNativeFlag
      (.seq (.op (.emit true)) emitFlagBit))))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: one physical signed input scan emits the exact strict
test conjunction in time linear in the native record width. -/
theorem inputFlagEntry_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (store : Fin MM) (width : ℕ) (z : ℤ) (bound : ℕ) (flag : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = frame (binary width (encS z)) ++ rest)
    (hz : encS z < 2 ^ width) (hwidth : width+2 ≤ C.Wd)
    (hb : a.env thresholdVar = bound) (hfour : 4 ≤ 2 ^ C.Wd)
    (hr : a.rc store < (a.ram store).length)
    (hflag : (a.ram store).getD (a.rc store) 0 = flag.toNat) :
    Hs C (inputFlagEntry store) a (12*width+32) (fun b =>
      b.ip = a.ip+(2*width+1) ∧
      b.out = a.out ++ [true,flag && decide (z < (bound:ℤ))] ∧
      b.ram = a.ram ∧ b.rc store = a.rc store+1 ∧
      (b.kin,b.kout,b.kc) = (a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]) := by
  unfold inputFlagEntry
  refine (Hs.seq (t2 := 19) (rdRec_spec a hc width (encS z) rest hin hz hwidth)
    fun b ⟨hbv,hbp,hbr,hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  refine Hs.seq (t2 := 17) (hs_copy C u4 t3 b (by decide)) fun d hd => ?_
  subst d
  let d := b.set u4 (b.env t3)
  have hdc : Cst d := Cst.of_fr (T := [u4]) hbc (Fr.set _ _ (by decide)) (by decide)
  have hbrm : b.ram = a.ram := congrArg (fun p => p.2.1) hbr
  have hbrc : b.rc = a.rc := congrArg (fun p => p.2.2.1) hbr
  have hrd : d.rc store < (d.ram store).length := by
    change b.rc store < (b.ram store).length
    rw [hbrc,hbrm];exact hr
  refine Hs.seq (t2 := 15) (hs_rdM C store flagVar d hrd) fun e he => ?_
  subst e
  let e := (d.set flagVar ((d.ram store).getD (d.rc store) 0)).adv store
  have hec : Cst e := by
    refine ⟨?_,?_,?_⟩ <;> simp (config := {decide := true}) [e,DS.adv,DS.set,hdc.z,hdc.one,hdc.two]
  have heu : e.env u4 = encS z := by
    simp (config := {decide := true}) [e,d,DS.adv,DS.set,hbv]
  have heb : e.env thresholdVar = bound := by
    have hh : b.env thresholdVar = bound := by rw [hbf _ (by decide),hb]
    simp (config := {decide := true}) [e,d,DS.adv,DS.set,hh]
  have hef : e.env flagVar = flag.toNat := by
    simp only [e,DS.adv,DS.set_env_self]
    change (b.ram store).getD (b.rc store) 0 = _
    rw [hbrm,hbrc,hflag]
  refine (Hs.seq (t2 := 4) (testNativeFlag_spec C e hec z bound flag heu heb hef hfour)
    fun f ⟨hff,hfs,hfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hfm := Same.of_sh hfs
  have hfc : Cst f := Cst.of_fr hec hfr (by decide)
  refine Hs.seq (t2 := 2) (hs_emit C true f) fun g hg => ?_
  subst g
  refine (emitFlagBit_spec C {f with out := f.out ++ [true]}
    ⟨hfc.z,hfc.one,hfc.two⟩ _ hff).mono le_rfl ?_
  rintro g rfl
  refine ⟨?_,?_,?_,?_,?_,⟨hfc.z,hfc.one,hfc.two⟩,?_⟩
  · change f.ip = _
    rw [hfm.ip]
    exact hbp
  · change (f.out ++ [true]) ++ [_] = _
    rw [hfm.out]
    have hbo : b.out = a.out := congrArg Prod.fst hbr
    simp only [e,d,DS.adv,DS.set,hbo,List.append_assoc]
    rfl
  · change f.ram = _
    rw [hfm.ram]
    exact hbrm
  · change f.rc store = _
    rw [hfm.rc]
    simp [e,d,DS.adv,hbrc]
  · change (f.kin,f.kout,f.kc) = _
    rw [hfm.kin,hfm.kout,hfm.kc]
    exact congrArg (fun p => (p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2)) hbr
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken hfr (by decide))))

end NearQuarticWires.StageCertTests
