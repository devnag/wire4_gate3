import Proof.Quartic.Reconstruct.PrintIdxRun

/-!
# Writing the stored words of a printed table

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (every printed table receives `prepWord` and the
framed coefficient table).

* `emitBitsS m i n`: write the `n` bits of store `m` at depth `2` (`emitBitsS_spec`), for `prepWord`;
* `emitFrameS m`: write the framed word whose bits are in store `m` at depth `2` (`emitFrameS_spec`), for the
  coefficient table.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {C : Ctx}

/-- Write the `n` bits of store `m` at depth `2`. -/
def emitBitsS (m : Fin MM) (i n : Fin VV) : St VV MM := emitStoreS m i n (emitBD 2 t3)

theorem decide_toNat (b : Bool) : decide (b.toNat = 1) = b := by cases b <;> rfl

/-- **Writing stored bits.** -/
theorem emitBitsS_spec (m : Fin MM) (i n : Fin VV) (hi : i ≠ vJ ∧ n ≠ vJ ∧ i ≠ n ∧ i ≠ t3 ∧ n ≠ t3)
    (hiC : vZ ≠ i ∧ v1 ≠ i ∧ v2 ≠ i) (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length)
    (w : List Bool) (hm : a.ram m = w.map Bool.toNat) (hn : a.env n = w.length) (hN : w.length < 2 ^ C.Wd) :
    Hs C (emitBitsS m i n) a (a.rc m + 1 + (w.length * (2 * 2 ^ 2 + 2 + 1 + 1 + 4) + 4) + 1)
      (fun b => OutMoved a b (marksD 2 w) [i, t3, vJ] ∧ Cst b) := by
  have h := emitStoreS_spec m i n (emitBD 2 t3) (fun v => bitD 2 (decide (v = 1))) [vJ] (2 * 2 ^ 2 + 2)
    ⟨by simpa using hi.1, by simpa using hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2⟩ (by decide) hiC
    (w.map Bool.toNat) (fun c cc cok _ => (emitBD_spec 2 t3 (by decide) c cc).mono le_rfl
      (fun d hd => ⟨OutMoved.of_wrote hd cok, hd.rc, hd.cst cc (by decide)⟩)) a hc hok hm (by simpa using hn)
    (by simpa using hN)
  refine h.mono (by simp) (fun b ⟨mv, cb⟩ => ⟨?_, cb⟩)
  rw [List.flatMap_map] at mv
  have e : w.flatMap (fun x => bitD 2 (decide (x.toNat = 1))) = marksD 2 w := by
    unfold marksD; congr 1; funext x; rw [decide_toNat]
  rw [e] at mv
  exact mv

/-- Write the framed word stored in `m` at depth `2`. -/
def emitFrameS (m : Fin MM) : St VV MM :=
  .seq (.op (.rwM m)) (.seq (.op (.zero fE)) (.loop (.lt fE v1) (.seq (.op (.rdM m fM)) (.seq (emitBD 2 fM)
    (.ite (.eq fM v1) (.seq (.op (.rdM m fB)) (emitBD 2 fB)) (.op (.inc fE)))))))

theorem frame_map_getD_end (u : List Bool) : ((frame u).map Bool.toNat).getD (2 * u.length) 0 = 0 := by
  induction u with
  | nil => rfl
  | cons b l ih =>
    rw [frame_cons']
    simp only [List.map_cons, List.length_cons]
    rw [show 2 * (l.length + 1) = 2 * l.length + 2 by ring]
    simpa using ih

theorem marksD_marks_take_succ (u : List Bool) (k : ℕ) (hk : k < u.length) :
    marksD 2 (marks (u.take (k + 1))) = marksD 2 (marks (u.take k)) ++ bitD 2 true ++ bitD 2 u[k] := by
  rw [marks_take_succ u k hk, marksD_append, marksD_cons, marksD_cons, marksD_nil, List.append_nil,
    List.append_assoc]

/-- **Writing a stored framed word.** -/
theorem emitFrameS_spec (m : Fin MM) (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length)
    (u : List Bool) (hm : a.ram m = (frame u).map Bool.toNat) (hW : 1 ≤ C.Wd) :
    Hs C (emitFrameS m) a (a.rc m + 1 + (1 + ((u.length + 1) * (26 + 2) + 2) + 1) + 1)
      (fun b => OutMoved a b (marksD 2 (frame u)) [fE, fM, fB, vJ] ∧ Cst b) := by
  set T : List (Fin VV) := [fE, fM, fB, vJ] with hT
  have hlen := frame_map_length u
  have h2W : 2 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  refine Hx.hs (Hs.then (rwM_spec' m a hok T) (fun b0 ⟨o0, r0, e0⟩ n0 hn0 => ?_))
  have c0 : Cst b0 := ⟨by rw [e0]; exact hc.z, by rw [e0]; exact hc.one, by rw [e0]; exact hc.two⟩
  let P : ℕ → DS VV MM → Prop := fun k b => Cst b ∧ (∀ m, b.rc m ≤ (b.ram m).length) ∧ b.ram = a.ram ∧
    b.ip = a.ip ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b T ∧
    (k ≤ u.length → b.env fE = 0 ∧ b.rc m = 2 * k ∧ b.out = a.out ++ marksD 2 (marks (u.take k))) ∧
    (u.length < k → b.env fE = 1 ∧ b.out = a.out ++ marksD 2 (frame u))
  have loop : ∀ b, P 0 b → Hs C (.loop (.lt fE v1) (.seq (.op (.rdM m fM)) (.seq (emitBD 2 fM)
      (.ite (.eq fM v1) (.seq (.op (.rdM m fB)) (emitBD 2 fB)) (.op (.inc fE)))))) b
      ((u.length + 1) * (26 + 2) + 2) (P (u.length + 1)) := by
    refine Hs.loopN (c := .lt fE v1) (show fE ≠ v1 by decide) P (u.length + 1) 26 ?_ ?_
    · intro k hk b ⟨hcb, hokb, hr, hi, hki, hko, hkc, hfr, h1, _⟩
      obtain ⟨e0', erc, eout⟩ := h1 (by omega)
      refine ⟨by simp [Cnd.eval, e0', hcb.one], ?_⟩
      have hl1 : b.rc m < (b.ram m).length := by rw [erc, hr, hm, hlen]; omega
      refine Hx.hs (Hs.then (rdM_spec' m fM b hl1 hokb) (fun b1 ⟨x1, x2, x3⟩ n1 hn1 => ?_))
      have c1 : Cst b1 := x3.cst hcb (by decide)
      refine Hs.then (emitBD_spec 2 fM (by decide) b1 c1) (fun b2 w2 n2 hn2 => ?_)
      have c2 : Cst b2 := w2.cst c1 (by decide)
      have m2 := (OutMoved.of_wrote w2 x3.rcok)
      have fM2 : b2.env fM = b1.env fM := m2.fr fM (by decide)
      rcases Nat.lt_or_ge k u.length with hku | hku
      · -- a data bit
        obtain ⟨g1, g2⟩ := frame_map_getD u k hku
        have v1' : b1.env fM = 1 := by rw [x1, erc, hr, hm]; exact g1
        have hl2 : b2.rc m < (b2.ram m).length := by
          rw [w2.rc, w2.ram, x2, x3.ram, erc, hr, hm, hlen]; omega
        refine Hs.last (Hs.iteT (t := 12) (show fM ≠ v1 by decide) (by simp [Cnd.eval, fM2, v1', c2.one])
          (Hx.hs (Hs.then (rdM_spec' m fB b2 hl2 m2.rcok) (fun b3 ⟨x4, x5, x6⟩ n3 hn3 =>
            Hs.last (emitBD_spec 2 fB (by decide) b3 (x6.cst c2 (by decide))) (fun b4 w4 n4 hn4 => ⟨?_, ?_⟩)))))
          (fun b5 h5 n5 hn5 => ⟨h5, by omega⟩)
        · have c4 : Cst b4 := w4.cst (x6.cst c2 (by decide)) (by decide)
          have fB4 : b3.env fB = (u[k]).toNat := by
            rw [x4, w2.rc, w2.ram, x2, x3.ram, erc, hr, hm]; exact g2
          have m4 := OutMoved.of_wrote w4 x6.rcok
          refine ⟨c4, m4.rcok, by rw [m4.ram, x6.ram, m2.ram, x3.ram, hr], by rw [m4.ip, x6.ip, m2.ip, x3.ip, hi],
            by rw [m4.kin, x6.kin, m2.kin, x3.kin, hki], by rw [m4.kout, x6.kout, m2.kout, x3.kout, hko],
            by rw [m4.kc, x6.kc, m2.kc, x3.kc, hkc], Fr.trans hfr (Fr.trans (x3.fr.weaken (by decide))
              (Fr.trans (m2.fr.weaken (by decide)) (Fr.trans (x6.fr.weaken (by decide)) (m4.fr.weaken (by decide))))),
            fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd h (by omega)⟩
          · rw [m4.fr fE (by decide), x6.fr fE (by decide), m2.fr fE (by decide), x3.fr fE (by decide), e0']
          · rw [w4.rc, x5, w2.rc, x2, erc]; ring
          · rw [m4.out, x6.out, m2.out, x3.out, eout, fB4, v1', decide_toNat, marksD_marks_take_succ u k hku]
            simp [List.append_assoc]
        · omega
      · -- the end mark
        have hk' : k = u.length := by omega
        subst hk'
        have v1' : b1.env fM = 0 := by rw [x1, erc, hr, hm]; exact frame_map_getD_end u
        have hE2 : b2.env fE = 0 := by rw [m2.fr fE (by decide), x3.fr fE (by decide), e0']
        refine Hs.last (Hs.iteF (show fM ≠ v1 by decide) (by simp [Cnd.eval, fM2, v1', c2.one])
          (hs_inc C fE b2 (by rw [hE2]; omega))) (fun b3 hb3 n3 hn3 => ⟨?_, by omega⟩)
        subst hb3
        refine ⟨⟨by vsimp [c2.z], by vsimp [c2.one], by vsimp [c2.two]⟩, by simpa using m2.rcok, by
          simp only [DS.set_ram]; rw [m2.ram, x3.ram, hr], by simp only [DS.set_ip]; rw [m2.ip, x3.ip, hi],
          by simp only [DS.set_kin]; rw [m2.kin, x3.kin, hki], by simp only [DS.set_kout]; rw [m2.kout, x3.kout, hko],
          by simp only [DS.set_kc]; rw [m2.kc, x3.kc, hkc], Fr.trans hfr (Fr.trans (x3.fr.weaken (by decide))
            (Fr.trans (m2.fr.weaken (by decide)) (Fr.set _ _ (by decide)))), fun h => absurd h (by omega),
          fun _ => ⟨by rw [DS.set_env_self, hE2], ?_⟩⟩
        simp only [DS.set_out]
        rw [m2.out, x3.out, eout, v1', List.take_length, frame_eq_marks, marksD_append]
        simp [marksD_cons, marksD_nil]
    · intro b ⟨hcb, _, _, _, _, _, _, _, _, h2⟩
      have := (h2 (by omega)).1
      simp [Cnd.eval, this, hcb.one]
  refine Hs.then (hs_zero C fE b0) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨⟨by vsimp [c0.z], by vsimp [c0.one], by vsimp [c0.two]⟩, by simpa using o0.rcok,
    by simp only [DS.set_ram]; exact o0.ram, by simp only [DS.set_ip]; exact o0.ip,
    by simp only [DS.set_kin]; exact o0.kin, by simp only [DS.set_kout]; exact o0.kout,
    by simp only [DS.set_kc]; exact o0.kc, Fr.trans o0.fr (Fr.set _ _ (by decide)),
    fun _ => ⟨DS.set_env_self _ _ _, by simpa using r0, by simp [o0.out, marks_eq_flatMap, marksD_nil]⟩,
    fun h => absurd h (by omega)⟩)
    (fun b ⟨c1, ok1, r1, i1, ki1, ko1, kc1, f1, _, h2⟩ n hn => ⟨⟨⟨(h2 (by omega)).2, i1, r1, ki1, ko1, kc1, f1, ok1⟩,
      c1⟩, by omega⟩)

end NearQuarticWires.Reconstruct
