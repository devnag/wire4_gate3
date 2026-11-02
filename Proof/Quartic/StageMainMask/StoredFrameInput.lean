import Proof.Quartic.StageMainMask.StoredInput
import Proof.Quartic.StageLift.FrameWrite

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
one actual retained witness bit and its frame marker are written to the
ordinary callee input by explicit source and output instructions. -/
def storedFrameInputBit (store : Fin MM) : St VV MM :=
  .seq (.op (.rdM store t0)) (.seq (.op (.kem true)) (emitB .kem t0))

/-- `prop:time`, paper/paper.tex: one original
stored witness bit is physically framed with its exact capacity guard. -/
theorem storedFrameInputBit_run (C : Ctx) (store : Fin MM) (a : DS VV MM)
    (hc : Cst a) (bit : Bool) (hlt : a.rc store < (a.ram store).length)
    (hv : (a.ram store).getD (a.rc store) 0 = bit.toNat)
    (hroom : a.kin.length + 2 ≤ C.Lk) :
    Hs C (storedFrameInputBit store) a 6 (fun b =>
      b.kin = a.kin ++ [true, bit] ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store (a.rc store + 1) ∧
      (b.out, b.kout, b.kc) = (a.out, a.kout, a.kc) ∧ Cst b ∧ Fr a b [t0]) := by
  unfold storedFrameInputBit
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_rdM C store t0 a hlt) ?_
  rintro b rfl
  let b := (a.set t0 ((a.ram store).getD (a.rc store) 0)).adv store
  have hbf : Fr a b [t0] := Fr.set a _ (by simp)
  have hbc : Cst b := hc.of_fr hbf (by decide)
  refine Hs.seq (t1 := 1) (t2 := 2) (hs_kem C true b (by change a.kin.length < C.Lk; omega)) ?_
  rintro d rfl
  refine (emitB_spec (snkK C) t0 (by decide) {b with kin := b.kin ++ [true]}
    ⟨hbc.z, hbc.one, hbc.two⟩ (by
      change (a.kin ++ [true]).length < C.Lk
      simp only [List.length_append, List.length_singleton]
      omega)).mono le_rfl ?_
  rintro d ⟨hdk, hdr, hde⟩
  have heq : decide (b.env t0 = 1) = bit := by
    simp only [b, DS.adv, DS.set_env_self, hv]
    cases bit <;> rfl
  refine ⟨?_, congrArg (fun t => t.1) hdr,
    congrArg (fun t => t.2.2.1) hdr, congrArg (fun t => t.2.2.2.1) hdr, ?_, ?_, ?_⟩
  · change d.kin = (b.kin ++ [true]) ++ [decide (b.env t0 = 1)] at hdk
    rw [heq] at hdk
    simpa only [b, DS.adv, DS.set, List.append_assoc, List.singleton_append] using hdk
  · exact congrArg (fun t => (t.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdr
  · exact ⟨(congrFun hde vZ).trans hbc.z, (congrFun hde v1).trans hbc.one,
      (congrFun hde v2).trans hbc.two⟩
  · intro x hx
    exact (congrFun hde x).trans (hbf x hx)

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the finite actual witness is copied to the callee with all ordinary
frame markers, using its measured runtime length. -/
def emitStoredFrameInput (store : Fin MM) (lengthRegister : Fin VV) : St VV MM :=
  .seq (.op (.rwM store))
    (.seq (forS c0 lengthRegister (storedFrameInputBit store)) (.op (.kem false)))

/-- `prop:time`, paper/paper.tex: the complete
original witness frame is physically emitted with every retained-source
read, marker write and rewind charged, including the empty frame. -/
theorem emitStoredFrameInput_run (C : Ctx) (store : Fin MM) (lengthRegister : Fin VV)
    (hlenreg : lengthRegister ∉ [c0, t0]) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram store = bits.map Bool.toNat) (hlen : a.env lengthRegister = bits.length)
    (hfit : bits.length < 2 ^ C.Wd) (hroom : a.kin.length + (frame bits).length ≤ C.Lk) :
    Hs C (emitStoredFrameInput store lengthRegister) a (a.rc store + 10 * bits.length + 8)
      (fun b => b.kin = a.kin ++ frame bits ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
        b.rc = Function.update a.rc store bits.length ∧
        (b.out, b.kout, b.kc) = (a.out, a.kout, a.kc) ∧ Cst b ∧ Fr a b [c0, t0]) := by
  have hc0 : c0 ≠ lengthRegister := by intro he; exact hlenreg (by simp [← he])
  have ht0 : lengthRegister ≠ t0 := by intro he; exact hlenreg (by simp [he])
  have hpairs (k : ℕ) (hk : k ≤ bits.length) :
      ((bits.take k).flatMap (fun bit => [true, bit])).length = 2 * k := by
    have hh := congrArg List.length (StageLift.frame_eq_pairs (bits.take k))
    simp only [frame_length, List.length_append, List.length_singleton, List.length_take,
      Nat.min_eq_left hk] at hh
    omega
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.kin = a.kin ++ (bits.take k).flatMap (fun bit => [true, bit]) ∧
    b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = Function.update a.rc store k ∧
    (b.out, b.kout, b.kc) = (a.out, a.kout, a.kc) ∧ Cst b ∧ Fr a b [c0, t0]
  have hf := forS_spec' (C := C) c0 lengthRegister hc0 (storedFrameInputBit store)
    (a.rew store) bits.length hfit I 6 ?_ ?_ hlen ?_
  · unfold emitStoredFrameInput
    refine (Hs.seq (t1 := a.rc store + 1) (t2 := 10 * bits.length + 6)
      (hs_rwM C store a) ?_).mono (by omega) (fun _ h => h)
    rintro b rfl
    refine Hs.seq (t1 := 10 * bits.length + 4) (t2 := 1) (hf.mono (by omega) (fun _ h => h)) ?_
    rintro b ⟨⟨hbk, hbi, hbr, hbrc, hbrest, hbc, hbfr⟩, _, _⟩
    refine (hs_kem C false b (by
      rw [hbk, List.length_append, hpairs _ le_rfl]
      rw [frame_length] at hroom
      omega)).mono le_rfl ?_
    rintro d rfl
    refine ⟨?_, hbi, hbr, hbrc, hbrest, ⟨hbc.z, hbc.one, hbc.two⟩, hbfr⟩
    rw [hbk, StageLift.frame_eq_pairs]
    simp only [List.take_length, List.append_assoc]
  · intro k b value ⟨hbk, hbi, hbr, hbrc, hbrest, hbc, hbfr⟩
    exact ⟨hbk, hbi, hbr, hbrc, hbrest,
      hbc.of_fr (Fr.set (T := [c0]) b value (by simp)) (by decide),
      hbfr.trans (Fr.set b value (by simp))⟩
  · exact ⟨by simp [DS.rew], rfl, rfl, rfl, rfl, ⟨hc.z, hc.one, hc.two⟩, Fr.refl _ _⟩
  · rintro k hk b ⟨hbk, hbi, hbr, hbrc, hbrest, hbc, hbfr⟩ hbindex hblen
    have hl : b.rc store < (b.ram store).length := by
      rw [hbr, hbits, List.length_map, hbrc, Function.update_self]
      exact hk
    have hv : (b.ram store).getD (b.rc store) 0 = (bits[k]).toNat := by
      rw [hbr, hbits, hbrc, Function.update_self, List.getD_eq_getElem _ _ (by simpa using hk)]
      simp only [List.getElem_map]
    refine (storedFrameInputBit_run C store b hbc bits[k] hl hv (by
      rw [hbk, List.length_append, hpairs _ hk.le]
      rw [frame_length] at hroom
      omega)).mono le_rfl ?_
    rintro d ⟨hdk, hdi, hdr, hdrc, hdrest, hdc, hdfr⟩
    refine ⟨⟨?_, hdi.trans hbi, hdr.trans hbr, ?_, hdrest.trans hbrest, hdc,
      hbfr.trans (hdfr.weaken (by simp))⟩, ?_, ?_⟩
    · rw [hdk, hbk, List.take_succ_eq_append_getElem hk, List.flatMap_append]
      simp only [List.flatMap_singleton, List.append_assoc]
    · rw [hdrc, hbrc, Function.update_self, Function.update_idem]
    · exact (hdfr _ (by decide)).trans hbindex
    · exact (hdfr _ (by simpa only [List.mem_singleton] using ht0)).trans hblen

end NearQuarticWires.StageMainMask
