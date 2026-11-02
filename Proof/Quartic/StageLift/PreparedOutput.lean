import Proof.Quartic.StageLift.PreparedCache

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print` and Step 3, paper/paper.tex: the once-retained preparation word is copied to
actual output, without framing it or writing a callee-input tape. -/
def emitPreparedWord : St VV MM :=
  .seq (.op (.rwM preparedStore))
    (forS c0 preparedLength (.seq (.op (.rdM preparedStore t0)) (emitB .emit t0)))

/-- `lem:print` and Step 3, paper/paper.tex: every raw preparation bit is physically output once,
with a paid store rewind and one real read per bit. No callee capacity
or precomputed source word is an additional runtime input. -/
theorem emitPreparedWord_spec (C : Ctx) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram preparedStore = bits.map Bool.toNat)
    (hlen : a.env preparedLength = bits.length) (hfit : bits.length < 2 ^ C.Wd) :
    Hs C emitPreparedWord a (a.rc preparedStore + 8 * bits.length + 6) (fun b =>
      b.out = a.out ++ bits ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc preparedStore bits.length ∧
      (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b [c0, t0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ bits.take k ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc preparedStore k ∧
      (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b [c0, t0]
  unfold emitPreparedWord
  refine (Hs.seq (t2 := 8 * bits.length + 4) (hs_rwM C preparedStore a)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine (forS_spec' (C := C) c0 preparedLength (by decide)
    (.seq (.op (.rdM preparedStore t0)) (emitB .emit t0)) (a.rew preparedStore)
    bits.length hfit I 4 ?_ ?_ hlen ?_).mono (by omega) ?_
  · intro k b value ⟨hbo, hbi, hbr, hbcursor, hbcallee, hbc, hbfr⟩
    exact ⟨hbo, hbi, hbr, hbcursor, hbcallee,
      Cst.of_fr hbc (Fr.set (T := [c0]) b value (by simp)) (by decide),
      hbfr.trans (Fr.set b value (by simp))⟩
  · exact ⟨by simp [DS.rew], rfl, rfl, rfl, rfl, ⟨hc.z, hc.one, hc.two⟩, Fr.refl _ _⟩
  · intro k hk b ⟨hbo, hbi, hbr, hbcursor, hbcallee, hbc, hbfr⟩ hindex hcount
    have hcursor : b.rc preparedStore = k := by rw [hbcursor, Function.update_self]
    have hrecord : (b.ram preparedStore).getD (b.rc preparedStore) 0 = (bits[k]).toNat := by
      rw [hcursor, hbr, hbits, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
    refine Hs.seq (t1 := 1) (t2 := 2)
      (hs_rdM C preparedStore t0 b (by rw [hcursor, hbr, hbits, List.length_map]; exact hk))
      fun d hd => ?_
    subst d
    let d := (b.set t0 ((b.ram preparedStore).getD (b.rc preparedStore) 0)).adv preparedStore
    have hdfr : Fr b d [t0] := Fr.set b _ (by simp)
    have hdc : Cst d := Cst.of_fr hbc hdfr (by decide)
    have hdbit : d.env t0 = (bits[k]).toNat := hrecord
    refine (emitB_spec (snkO C) t0 (by decide) d hdc trivial).mono le_rfl ?_
    rintro e ⟨heo, herest, heenv⟩
    have hebit : decide (d.env t0 = 1) = bits[k] := by rw [hdbit]; cases bits[k] <;> rfl
    change e.out = d.out ++ [decide (d.env t0 = 1)] at heo
    change (e.ip, e.ram, e.rc, e.kin, e.kout, e.kc) =
      (d.ip, d.ram, d.rc, d.kin, d.kout, d.kc) at herest
    have heip := congrArg (fun t => t.1) herest
    have heram := congrArg (fun t => t.2.1) herest
    have herc : e.rc = d.rc := congrArg (fun t => t.2.2.1) herest
    have hecallee := congrArg (fun t => (t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) herest
    have hefr : Fr d e [c0, t0] := fun y _ => congrFun heenv y
    refine ⟨⟨?_, heip.trans hbi, heram.trans hbr, ?_, hecallee.trans hbcallee,
      ?_, hbfr.trans ((hdfr.weaken (by simp)).trans hefr)⟩, ?_, ?_⟩
    · rw [heo, hebit]
      change b.out ++ [bits[k]] = _
      rw [hbo, List.take_succ_eq_append_getElem hk, List.append_assoc]
    · rw [herc]
      simp only [d, DS.adv, DS.set, hbcursor, hcursor, Function.update_idem, Function.update_self]
    · exact ⟨(congrFun heenv vZ).trans hdc.z, (congrFun heenv v1).trans hdc.one,
        (congrFun heenv v2).trans hdc.two⟩
    · exact (congrFun heenv c0).trans ((hdfr _ (by decide)).trans hindex)
    · exact (congrFun heenv preparedLength).trans ((hdfr _ (by decide)).trans hcount)
  · rintro b ⟨⟨hbo, hbi, hbr, hbcursor, hbcallee, hbc, hbfr⟩, _hindex, _hcount⟩
    exact ⟨by simpa using hbo, hbi, hbr, hbcursor, hbcallee, hbc, hbfr⟩

end NearQuarticWires.StageLift
