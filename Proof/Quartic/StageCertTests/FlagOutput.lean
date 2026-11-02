import Proof.Quartic.StageCertTests.FlagArithmetic
import Proof.Quartic.StageRecovery.PacketList
import Proof.Quartic.StageCert.CopyPayload

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery (countVar)

/-- `sec:algorithm`, paper/paper.tex:
one stored conjunction bit is emitted as a physical Boolean. -/
def emitFlagBit : St VV MM :=
  .ite (.eq flagVar v1) (.op (.emit true)) (.op (.emit false))

/-- `sec:algorithm`, paper/paper.tex:
the branch emits exactly the stored Boolean, including false. -/
theorem emitFlagBit_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (flag : Bool)
    (hf : a.env flagVar = flag.toNat) :
    Hs C emitFlagBit a 2 (fun b => b = {a with out := a.out ++ [flag]}) := by
  unfold emitFlagBit
  cases flag
  · refine Hs.ite (show flagVar ≠ v1 by decide) (fun h => ?_) (fun _ => hs_emit C false a)
    simp [Cnd.eval,hf,hc.one] at h
  · refine Hs.ite (show flagVar ≠ v1 by decide) (fun _ => hs_emit C true a) (fun h => ?_)
    simp [Cnd.eval,hf,hc.one] at h

/-- `sec:algorithm`, paper/paper.tex:
one sequential store read emits the marker and the exact certificate bit. -/
def emitStoredFlag (store : Fin MM) : St VV MM :=
  .seq (.op (.rdM store flagVar)) (.seq (.op (.emit true)) emitFlagBit)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: one framed bit costs constant source time,
preserving the call, witness, stores and all unrelated registers. -/
theorem emitStoredFlag_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (store : Fin MM) (flag : Bool) (hr : a.rc store < (a.ram store).length)
    (hf : (a.ram store).getD (a.rc store) 0 = flag.toNat) :
    Hs C (emitStoredFlag store) a 6 (fun b =>
      b.out = a.out ++ [true,flag] ∧ b.ram = a.ram ∧ b.rc store = a.rc store+1 ∧
      (b.ip,b.kin,b.kout,b.kc) = (a.ip,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [flagVar]) := by
  unfold emitStoredFlag
  refine Hs.seq (t2 := 4) (hs_rdM C store flagVar a hr) fun b he => ?_
  subst b
  let d := (a.set flagVar ((a.ram store).getD (a.rc store) 0)).adv store
  have hdc : Cst d := by
    refine ⟨?_,?_,?_⟩ <;> simp (config := {decide := true}) [d,DS.adv,DS.set,hc.z,hc.one,hc.two]
  have hdf : d.env flagVar = flag.toNat := by
    change (a.ram store).getD (a.rc store) 0 = _
    exact hf
  refine Hs.seq (t2 := 2) (hs_emit C true d) fun b he => ?_
  subst b
  refine (emitFlagBit_spec C {d with out := d.out ++ [true]}
    ⟨hdc.z,hdc.one,hdc.two⟩ flag hdf).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_,rfl,?_,rfl,⟨hdc.z,hdc.one,hdc.two⟩,?_⟩
  · simp [d,DS.adv,List.append_assoc]
  · simp [d,DS.adv]
  · exact Fr.set _ _ (by decide)

/-- `sec:algorithm`, paper/paper.tex:
only the original center prefix is emitted from the padded flag array. -/
def emitFlagPrefix (store : Fin MM) : St VV MM :=
  .seq (forS c0 countVar (emitStoredFlag store)) (.op (.emit false))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the final bitmap crop is one linear prefix scan,
including every frame marker and the final terminator. -/
theorem emitFlagPrefix_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (store : Fin MM) (flags : List Bool) (count : ℕ) (hcount : count ≤ flags.length)
    (hflags : a.ram store = flags.map Bool.toNat) (hr : a.rc store = 0)
    (hn : a.env countVar = count) (hnfit : count < 2 ^ C.Wd) :
    Hs C (emitFlagPrefix store) a (10*count+6) (fun b =>
      b.out = a.out ++ frame (flags.take count) ∧ b.ram = a.ram ∧ b.rc store = count ∧ Cst b) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ (flags.take k).flatMap (fun flag => [true,flag]) ∧
    b.ram = a.ram ∧ b.rc store = k ∧ Cst b
  have hloop : Hs C (forS c0 countVar (emitStoredFlag store)) a (count*(6+4)+4)
      (fun b => I count b) := by
    refine (forS_spec' c0 countVar (by decide) (emitStoredFlag store) a count hnfit I 6
      (fun k b v ⟨hbo,hbr,hbc,hbz⟩ => ?_)
      ⟨by simp,rfl,hr,hc⟩ hn ?_).mono le_rfl (fun _ h => h.1)
    · exact ⟨hbo,hbr,hbc,Cst.of_fr (T := [c0]) hbz (Fr.set _ _ (by decide)) (by decide)⟩
    · intro k hk b ⟨hbo,hbr,hbc,hbz⟩ hbctr hbn
      have hkl : k < flags.length := by omega
      have hrd : b.rc store < (b.ram store).length := by rw [hbc,hbr,hflags,List.length_map];exact hkl
      have hbit : (b.ram store).getD (b.rc store) 0 = flags[k].toNat := by
        rw [hbr,hflags,hbc,List.getD_eq_getElem _ _ (by simp;omega),List.getElem_map]
      refine (emitStoredFlag_spec C b hbz store flags[k] hrd hbit).mono le_rfl ?_
      rintro d ⟨hdo,hdr,hdc,_,hdz,hdf⟩
      refine ⟨⟨?_,hdr.trans hbr,by rw [hdc,hbc],hdz⟩,
        by rw [hdf _ (by decide),hbctr],by rw [hdf _ (by decide),hbn]⟩
      rw [hdo,hbo,List.take_succ_eq_append_getElem hkl,List.flatMap_append,
        List.flatMap_singleton,List.append_assoc]
  unfold emitFlagPrefix
  refine (Hs.seq (t2 := 1) hloop fun b ⟨hbo,hbr,hbc,hbz⟩ => ?_).mono (by omega) (fun _ h => h)
  refine (hs_emit C false b).mono le_rfl ?_
  rintro d rfl
  refine ⟨?_,hbr,hbc,⟨hbz.z,hbz.one,hbz.two⟩⟩
  rw [hbo]
  simp only [List.append_assoc]
  rw [StageCert.frame_eq_body]
  rfl

end NearQuarticWires.StageCertTests
