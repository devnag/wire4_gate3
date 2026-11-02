import Proof.Quartic.StageMain.CompactEmit

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:algorithm`, paper/paper.tex: the retained original call is copied bit for bit to the finite arithmetic request. -/
def emitStoredWord (store : Fin MM) (lengthRegister : Fin VV) : St VV MM := .seq (.op (.rwM store))
  (forS c0 lengthRegister (.seq (.op (.rdM store t0)) (emitB .emit t0)))

/-- `prop:time`, paper/paper.tex: every retained source read, rewind and literal output write is charged linearly. -/
theorem emitStoredWord_run (C : Ctx) (store : Fin MM) (lengthRegister : Fin VV)
    (hlenreg : lengthRegister ∉ [c0, t0]) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram store = bits.map Bool.toNat)
    (hlen : a.env lengthRegister = bits.length) (hfit : bits.length < 2 ^ C.Wd)
    : Hs C (emitStoredWord store lengthRegister) a (a.rc store + 8 * bits.length + 6) (fun b =>
      b.out = a.out ++ bits ∧ b.ip = a.ip ∧ b.kin = a.kin ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store bits.length ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b [c0, t0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ bits.take k ∧ b.ip = a.ip ∧ b.kin = a.kin ∧ b.ram = a.ram ∧
    b.rc = Function.update a.rc store k ∧
    b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b [c0, t0]
  have hc0 : c0 ≠ lengthRegister := by intro h; exact hlenreg (by simp [← h])
  have ht0 : lengthRegister ≠ t0 := by intro h; exact hlenreg (by simp [h])
  unfold emitStoredWord
  refine (Hs.seq (t2 := 8 * bits.length + 4) (hs_rwM C store a) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  refine (forS_spec' (C := C) c0 lengthRegister hc0
    (.seq (.op (.rdM store t0)) (emitB .emit t0)) (a.rew store)
    bits.length hfit I 4 ?_ ?_ hlen ?_).mono (by omega) ?_
  · intro k b value ⟨hbi, hbp, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩
    exact ⟨hbi, hbp, hbo, hbr, hbcurs, hbk, hbkc,
      Cst.of_fr hbc (Fr.set (T := [c0]) b value (by simp)) (by decide),
      hbf.trans (Fr.set b value (by simp))⟩
  · exact ⟨by simp [DS.rew], rfl, rfl, rfl, rfl, rfl, rfl, ⟨hc.z, hc.one, hc.two⟩, Fr.refl _ _⟩
  · intro k hk b ⟨hbkin, hbip, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩ hbi hbl
    have hcursor : b.rc store = k := by rw [hbcurs, Function.update_self]
    have hrecord : (b.ram store).getD (b.rc store) 0 = (bits[k]).toNat := by
      rw [hcursor, hbr, hbits, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
    refine Hs.seq (t1 := 1) (t2 := 2)
      (hs_rdM C store t0 b (by rw [hcursor, hbr, hbits, List.length_map]; exact hk)) ?_
    rintro d rfl
    let d := (b.set t0 ((b.ram store).getD (b.rc store) 0)).adv store
    have hdf : Fr b d [t0] := Fr.set b _ (by simp)
    have hdc := Cst.of_fr hbc hdf (by decide)
    have hdt : d.env t0 = (bits[k]).toNat := by
      change (b.ram store).getD (b.rc store) 0 = _
      exact hrecord
    have hki : d.out = a.out ++ bits.take k := hbkin
    refine (emitB_spec (snkO C) t0 (by decide) d hdc trivial).mono le_rfl ?_
    rintro e ⟨hekin, herest, heenv⟩
    have hebit : decide (d.env t0 = 1) = bits[k] := by rw [hdt]; cases bits[k] <;> rfl
    change e.out = d.out ++ [decide (d.env t0 = 1)] at hekin
    change (e.ip, e.ram, e.rc, e.kin, e.kout, e.kc) = (d.ip, d.ram, d.rc, d.kin, d.kout, d.kc) at herest
    have heip := congrArg (fun t => t.1) herest
    have heout := congrArg (fun t => t.2.2.2.1) herest
    have heram := congrArg (fun t => t.2.1) herest
    have herc : e.rc = d.rc := congrArg (fun t => t.2.2.1) herest
    have hekout := congrArg (fun t => t.2.2.2.2.1) herest
    have hekc := congrArg (fun t => t.2.2.2.2.2) herest
    have hef : Fr d e [c0, t0] := fun y _ => congrFun heenv y
    refine ⟨⟨?_, heip.trans hbip, heout.trans hbo, heram.trans hbr, ?_, hekout.trans hbk,
      hekc.trans hbkc, ?_, hbf.trans ((hdf.weaken (by simp)).trans hef)⟩, ?_, ?_⟩
    · rw [hekin, hebit, hki, List.take_succ_eq_append_getElem hk, List.append_assoc]
    · rw [herc]
      change Function.update b.rc store (b.rc store + 1) = _
      rw [hbcurs, Function.update_self, Function.update_idem]
    · exact Cst.of_fr hdc hef (by decide)
    · rw [heenv]
      exact (hdf c0 (by decide)).trans hbi
    · rw [heenv]
      exact (hdf lengthRegister (by simpa only [List.mem_singleton] using ht0)).trans hbl
  · rintro b ⟨⟨hbkin, hbip, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩, _, _⟩
    exact ⟨by simpa using hbkin, hbip, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩


end NearQuarticWires.StageMainMask
