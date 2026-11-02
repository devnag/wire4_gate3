import Proof.Quartic.StageMain.CompactPrepare

/-!
# Reusing the compact preparation word in sample calls

Step 4 of `sec:algorithm`, paper/paper.tex,
uses only the retained finite preparation word for each sample call.
The record-store rewind and each actual callee-input write are charged;
the original certificate-stream cursor remains unchanged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

def emitCompact : St VV MM := .seq (.op (.rwM compactStore))
  (forS c0 compactLength (.seq (.op (.rdM compactStore t0)) (emitB .kem t0)))

theorem emitCompact_run (C : Ctx) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram compactStore = bits.map Bool.toNat)
    (hlen : a.env compactLength = bits.length) (hfit : bits.length < 2 ^ C.Wd)
    (hroom : a.kin.length + bits.length ≤ C.Lk) :
    Hs C emitCompact a (a.rc compactStore + 8 * bits.length + 6) (fun b =>
      b.kin = a.kin ++ bits ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc compactStore bits.length ∧
      b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b [c0, t0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.kin = a.kin ++ bits.take k ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
    b.rc = Function.update a.rc compactStore k ∧
    b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b [c0, t0]
  unfold emitCompact
  refine (Hs.seq (t2 := 8 * bits.length + 4) (hs_rwM C compactStore a) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  refine (forS_spec' (C := C) c0 compactLength (by decide)
    (.seq (.op (.rdM compactStore t0)) (emitB .kem t0)) (a.rew compactStore)
    bits.length hfit I 4 ?_ ?_ hlen ?_).mono (by omega) ?_
  · intro k b value ⟨hbi, hbp, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩
    exact ⟨hbi, hbp, hbo, hbr, hbcurs, hbk, hbkc,
      Cst.of_fr hbc (Fr.set (T := [c0]) b value (by simp)) (by decide),
      hbf.trans (Fr.set b value (by simp))⟩
  · exact ⟨by simp [DS.rew], rfl, rfl, rfl, rfl, rfl, rfl, ⟨hc.z, hc.one, hc.two⟩, Fr.refl _ _⟩
  · intro k hk b ⟨hbkin, hbip, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩ hbi hbl
    have hcursor : b.rc compactStore = k := by rw [hbcurs, Function.update_self]
    have hrecord : (b.ram compactStore).getD (b.rc compactStore) 0 = (bits[k]).toNat := by
      rw [hcursor, hbr, hbits, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
    refine Hs.seq (t1 := 1) (t2 := 2)
      (hs_rdM C compactStore t0 b (by rw [hcursor, hbr, hbits, List.length_map]; exact hk)) ?_
    rintro d rfl
    let d := (b.set t0 ((b.ram compactStore).getD (b.rc compactStore) 0)).adv compactStore
    have hdf : Fr b d [t0] := Fr.set b _ (by simp)
    have hdc := Cst.of_fr hbc hdf (by decide)
    have hdt : d.env t0 = (bits[k]).toNat := by
      change (b.ram compactStore).getD (b.rc compactStore) 0 = _
      exact hrecord
    have hki : d.kin = a.kin ++ bits.take k := hbkin
    refine (emitB_spec (snkK C) t0 (by decide) d hdc (by
      change d.kin.length < C.Lk
      rw [hki, List.length_append, List.length_take, Nat.min_eq_left hk.le]
      omega)).mono le_rfl ?_
    rintro e ⟨hekin, herest, heenv⟩
    have hebit : decide (d.env t0 = 1) = bits[k] := by rw [hdt]; cases bits[k] <;> rfl
    change e.kin = d.kin ++ [decide (d.env t0 = 1)] at hekin
    change (e.ip, e.out, e.ram, e.rc, e.kout, e.kc) = (d.ip, d.out, d.ram, d.rc, d.kout, d.kc) at herest
    have heip := congrArg (fun t => t.1) herest
    have heout := congrArg (fun t => t.2.1) herest
    have heram := congrArg (fun t => t.2.2.1) herest
    have herc : e.rc = d.rc := congrArg (fun t => t.2.2.2.1) herest
    have hekout := congrArg (fun t => t.2.2.2.2.1) herest
    have hekc := congrArg (fun t => t.2.2.2.2.2) herest
    have hef : Fr d e [c0, t0] := fun y _ => congrFun heenv y
    refine ⟨⟨?_, heip.trans hbip, heout.trans hbo, heram.trans hbr, ?_, hekout.trans hbk,
      hekc.trans hbkc, ?_, hbf.trans ((hdf.weaken (by simp)).trans hef)⟩, ?_, ?_⟩
    · rw [hekin, hebit, hki, List.take_succ_eq_append_getElem hk, List.append_assoc]
    · rw [herc]
      change Function.update b.rc compactStore (b.rc compactStore + 1) = _
      rw [hbcurs, Function.update_self, Function.update_idem]
    · exact Cst.of_fr hdc hef (by decide)
    · rw [heenv]
      exact (hdf c0 (by decide)).trans hbi
    · rw [heenv]
      exact (hdf compactLength (by decide)).trans hbl
  · rintro b ⟨⟨hbkin, hbip, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩, _, _⟩
    exact ⟨by simpa using hbkin, hbip, hbo, hbr, hbcurs, hbk, hbkc, hbc, hbf⟩

end NearQuarticWires.StageMain.Compact
