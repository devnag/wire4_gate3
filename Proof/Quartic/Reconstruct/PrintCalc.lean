import Proof.Quartic.Reconstruct.PrintWrite

/-!
# The numbers of the context computed by the printing stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `sec:params`.

* `calcA`: the last digit index `J - 1` and the bit of two circuits (`calcA_spec`);
* `calcB`: the number of columns `2^{n-k}` (`calcB_spec`);
* `calcC`: the number of tables per group, `Σ_p p` or `Σ_p p²` over the primes of the store `sPr` (`calcC_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- A counter. -/
def kT2 : Fin VV := ⟨101, by decide⟩
/-- A loop index. -/
def kI : Fin VV := ⟨102, by decide⟩

/-- `J - 1` and the bit of two circuits. -/
def calcA : St VV MM :=
  .seq (.op (.copy kJ kJ1)) (.seq (.op (.sub kJ v1)) (.ite (.eq kKd v1) (.op (.copy kPair v1)) (.op (.zero kPair))))

theorem calcA_spec (a : DS VV MM) (hc : Cst a) (J kd : ℕ) (hJ : a.env kJ1 = J) (hJ1 : 1 ≤ J) (hk : a.env kKd = kd) :
    Hs C calcA a 6 (fun b => b.env kJ = J - 1 ∧ b.env kPair = (if kd = 1 then 1 else 0) ∧ Same a b ∧
      Fr a b [kJ, kPair] ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_copy C kJ kJ1 a (by decide)) (fun b1 hb1 n1 hn1 => ?_))
  subst hb1
  refine Hs.then (hs_sub C kJ v1 _ (by decide) (by vsimp [hJ, hc.one]; omega)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  set b2 := (a.set kJ (a.env kJ1)).set kJ ((a.set kJ (a.env kJ1)).env kJ - (a.set kJ (a.env kJ1)).env v1) with hb2
  have e2 : b2.env kJ = J - 1 := by rw [hb2]; vsimp [hJ, hc.one]
  have k2 : b2.env kKd = kd := by rw [hb2]; vsimp [hk]
  have c2 : Cst b2 := ⟨by rw [hb2]; vsimp [hc.z], by rw [hb2]; vsimp [hc.one], by rw [hb2]; vsimp [hc.two]⟩
  have s2 : Same a b2 := (Same.set _ _ _).trans (Same.set _ _ _)
  have f2 : Fr a b2 [kJ, kPair] := (Fr.set a _ (by decide)).trans (Fr.set _ _ (by decide))
  refine Hs.last (Hs.ite (t := 1) (show kKd ≠ v1 by decide) (fun he => ?_) (fun he => ?_)) (fun b hb n hn => ⟨hb, by omega⟩)
  · have h1 : kd = 1 := by simpa [Cnd.eval, k2, c2.one] using he
    refine Hs.mono (hs_copy C kPair v1 b2 (by decide)) le_rfl ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide), e2], by rw [DS.set_env_self, c2.one, if_pos h1],
      s2.trans (Same.set _ _ _), f2.trans (Fr.set _ _ (by decide)), ⟨by vsimp [c2.z], by vsimp [c2.one], by vsimp [c2.two]⟩⟩
  · have h1 : kd ≠ 1 := by simpa [Cnd.eval, k2, c2.one] using he
    refine Hs.mono (hs_zero C kPair b2) le_rfl ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide), e2], by rw [DS.set_env_self, if_neg h1],
      s2.trans (Same.set _ _ _), f2.trans (Fr.set _ _ (by decide)), ⟨by vsimp [c2.z], by vsimp [c2.one], by vsimp [c2.two]⟩⟩

/-- The number of columns `2^{n-k}`. -/
def calcB : St VV MM :=
  .seq (.ite (.lt kN kK) (.op (.zero kT2)) (.seq (.op (.copy kT2 kN)) (.op (.sub kT2 kK))))
    (.seq (.op (.copy kC v1)) (.loop (.lt vZ kT2) (.seq (.op (.shl kC)) (.op (.sub kT2 v1)))))

theorem calcB_spec (a : DS VV MM) (hc : Cst a) (n k : ℕ) (hn : a.env kN = n) (hk : a.env kK = k)
    (hW : 2 ^ (n - k) < 2 ^ C.Wd) :
    Hs C calcB a ((n - k) * 5 + 9) (fun b => b.env kC = 2 ^ (n - k) ∧ Same a b ∧ Fr a b [kT2, kC] ∧ Cst b) := by
  -- the counter
  have hcnt : Hs C (.ite (.lt kN kK) (.op (.zero kT2)) (.seq (.op (.copy kT2 kN)) (.op (.sub kT2 kK)))) a 4
      (fun b => b.env kT2 = n - k ∧ Same a b ∧ Fr a b [kT2, kC] ∧ Cst b) := by
    refine Hs.ite (t := 3) (show kN ≠ kK by decide) (fun he => ?_) (fun he => ?_)
    · have h1 : n < k := by simpa [Cnd.eval, hn, hk] using he
      refine Hs.mono (hs_zero C kT2 a) (by norm_num) ?_
      rintro b rfl
      exact ⟨by rw [DS.set_env_self]; omega, Same.set _ _ _, Fr.set _ _ (by decide),
        ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩
    · have h1 : k ≤ n := by simpa [Cnd.eval, hn, hk] using he
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C kT2 kN a (by decide)) (fun b1 hb1 => ?_)
      subst hb1
      refine Hs.mono (hs_sub C kT2 kK _ (by decide) (by vsimp [hn, hk]; omega)) le_rfl ?_
      rintro b rfl
      exact ⟨by vsimp [hn, hk], (Same.set _ _ _).trans (Same.set _ _ _),
        (Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide)), ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩
  refine Hx.hs (Hs.then hcnt (fun b1 ⟨e1, s1, f1, c1⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C kC v1 b1 (by decide)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  let I : ℕ → DS VV MM → Prop := fun j b => b.env kT2 = (n - k) - j ∧ b.env kC = 2 ^ j ∧ Same a b ∧
    Fr a b [kT2, kC] ∧ Cst b
  have loop := Hs.loopN (C := C) (c := .lt vZ kT2) (s := .seq (.op (.shl kC)) (.op (.sub kT2 v1)))
    (show vZ ≠ kT2 by decide) I (n - k) 3 (fun j hj b ⟨h1, h2, h3, h4, h5⟩ => by
      refine ⟨by simp [Cnd.eval, h1, h5.z]; omega, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C kC b (by
        rw [h2, ← pow_succ']; exact lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by omega)) hW)) (fun b1 hb1 => ?_)
      subst hb1
      refine Hs.mono (hs_sub C kT2 v1 _ (by decide) (by vsimp [h1, h5.one]; omega)) le_rfl ?_
      rintro c rfl
      exact ⟨by vsimp [h1, h5.one]; omega, by vsimp [h2]; rw [pow_succ]; ring, (h3.trans (Same.set _ _ _)).trans
        (Same.set _ _ _), (h4.trans (Fr.set _ _ (by decide))).trans (Fr.set _ _ (by decide)),
        ⟨by vsimp [h5.z], by vsimp [h5.one], by vsimp [h5.two]⟩⟩)
    (fun b ⟨h1, _, _, _, h5⟩ => by simp [Cnd.eval, h1, h5.z])
  refine Hs.last (loop _ ⟨by vsimp [e1], by vsimp [c1.one], s1.trans (Same.set _ _ _),
    f1.trans (Fr.set _ _ (by decide)), ⟨by vsimp [c1.z], by vsimp [c1.one], by vsimp [c1.two]⟩⟩)
    (fun b ⟨_, h2, h3, h4, h5⟩ m hm => ⟨⟨h2, h3, h4, h5⟩, by omega⟩)

/-- The number of tables per group: `Σ_p p` (one circuit) or `Σ_p p²` (two circuits) over the store `sPr`. -/
def calcC : St VV MM :=
  .seq (.op (.zero kG)) (.seq (.op (.rwM sPr)) (forS kI kPc (.seq (.op (.rdM sPr t3))
    (.ite (.eq kPair v1) (.seq (.op (.copy t4 t3)) (.seq (.op (.mul t3 t4 t0)) (.op (.add kG t0))))
      (.op (.add kG t3))))))

/-- The size of the residue vectors modulo `p`. -/
def groupSize (pb p : ℕ) : ℕ := if pb = 1 then p * p else p

theorem calcC_spec (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length) (ps : List ℕ) (pb : ℕ)
    (hps : a.ram sPr = ps) (hn : a.env kPc = ps.length) (hpb : a.env kPair = pb)
    (hbig : (ps.map (groupSize pb)).sum < 2 ^ C.Wd) (hsq : ∀ p ∈ ps, p * p < 2 ^ C.Wd)
    (hN : ps.length < 2 ^ C.Wd) :
    Hs C calcC a (a.rc sPr + 1 + (ps.length * (8 + 4) + 4) + 3)
      (fun b => b.env kG = (ps.map (groupSize pb)).sum ∧ b.out = a.out ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
        b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [kG, kI, t0, t3, t4] ∧ (∀ m, b.rc m ≤ (b.ram m).length) ∧
        Cst b) := by
  refine Hx.hs (Hs.then (hs_zero C kG a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hok0 : ∀ m, (a.set kG 0).rc m ≤ ((a.set kG 0).ram m).length := hok
  refine Hs.then (rwM_spec' sPr (a.set kG 0) hok0 [kG, kI, t0, t3, t4]) (fun b1 ⟨o1, r1, e1⟩ n1 hn1 => ?_)
  have c1 : Cst b1 := ⟨by rw [e1]; vsimp [hc.z], by rw [e1]; vsimp [hc.one], by rw [e1]; vsimp [hc.two]⟩
  let Inv : ℕ → DS VV MM → Prop := fun k b => b.env kG = ((ps.take k).map (groupSize pb)).sum ∧ b.rc sPr = k ∧
    b.out = a.out ∧ b.ip = a.ip ∧ b.ram = a.ram ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
    Fr a b [kG, kI, t0, t3, t4] ∧ (∀ m, b.rc m ≤ (b.ram m).length) ∧ Cst b
  have hset : ∀ k b v, Inv k b → Inv k (b.set kI v) := fun k b v ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ =>
    ⟨by rw [DS.set_env_ne _ _ (by decide), h1], h2, h3, h4, h5, h6, h7, h8, Fr.trans h9 (Fr.set b v (by decide)), h10,
      ⟨by vsimp [h11.z], by vsimp [h11.one], by vsimp [h11.two]⟩⟩
  refine Hs.last (forS_spec kI kPc (by decide) _ ps.length 8 (fun _ => []) Inv hset ?_ b1
    ⟨by rw [e1]; vsimp [], r1, by rw [o1.out]; simp, by rw [o1.ip]; rfl, by rw [o1.ram]; rfl, by rw [o1.kin]; rfl,
      by rw [o1.kout]; rfl, by rw [o1.kc]; rfl, (Fr.set a _ (by decide)).trans o1.fr, o1.rcok, c1⟩
    (by rw [e1]; vsimp [hn]) hN)
    (fun b ⟨⟨h1, _, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, _, _⟩ m hm =>
      ⟨⟨by rw [h1, List.take_length], h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, by simp only [DS.set_rc] at hn1; omega⟩)
  intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ hik hnk
  have hlt : b.rc sPr < (b.ram sPr).length := by rw [h2, h5, hps]; exact hk
  have hpk := List.getElem_mem hk
  have hgk : ps.getD k 0 = ps[k] := List.getD_eq_getElem _ _ hk
  have hsum : ((ps.take (k + 1)).map (groupSize pb)).sum = ((ps.take k).map (groupSize pb)).sum +
      groupSize pb ps[k] := by
    rw [List.take_succ_eq_append_getElem hk, List.map_append, List.sum_append]; simp
  have hle : ((ps.take (k + 1)).map (groupSize pb)).sum ≤ (ps.map (groupSize pb)).sum := by
    have := List.take_append_drop (k + 1) ps
    conv_rhs => rw [← this]
    rw [List.map_append, List.sum_append]; omega
  have hstep : ((ps.take k).map (groupSize pb)).sum + groupSize pb ps[k] < 2 ^ C.Wd := by rw [← hsum]; omega
  refine Hx.hs (Hs.then (rdM_spec' sPr t3 b hlt h10) (fun c ⟨x1, x2, x3⟩ n2 hn2 => ?_))
  rw [h2, h5, hps, hgk] at x1
  have cc : Cst c := x3.cst h11 (by decide)
  have pc : c.env kPair = pb := by rw [x3.fr kPair (by decide), h9 kPair (by decide), hpb]
  have gc : c.env kG = ((ps.take k).map (groupSize pb)).sum := by rw [x3.fr kG (by decide), h1]
  have ic : c.env kI = k := by rw [x3.fr kI (by decide), hik]
  have nc : c.env kPc = ps.length := by rw [x3.fr kPc (by decide), hnk]
  have common : ∀ d : DS VV MM, (∀ y, y ∉ [kG, t0, t4] → d.env y = c.env y) → d.out = c.out → d.ip = c.ip →
      d.ram = c.ram → d.rc = c.rc → d.kin = c.kin → d.kout = c.kout → d.kc = c.kc →
      d.env kG = ((ps.take (k + 1)).map (groupSize pb)).sum →
      Inv (k + 1) d ∧ d.env kI = k ∧ d.env kPc = ps.length ∧ d.out = b.out ++ [] := by
    intro d f1 o1 i1 r1 q1 k1 k2 k3 g1
    refine ⟨⟨g1, by rw [q1, x2, h2], by rw [o1, x3.out, h3, List.append_nil], by rw [i1, x3.ip, h4],
      by rw [r1, x3.ram, h5], by rw [k1, x3.kin, h6], by rw [k2, x3.kout, h7], by rw [k3, x3.kc, h8], ?_,
      fun m => by rw [q1, r1]; exact x3.rcok m, Cst.of_fr cc (fun y hy => f1 y hy) (by decide)⟩,
      by rw [f1 kI (by decide), ic], by rw [f1 kPc (by decide), nc], by rw [o1, x3.out]⟩
    intro y hy
    rw [f1 y (fun h => hy (by simp at h ⊢; tauto)), x3.fr y (fun h => hy (by simp at h ⊢; tauto)),
      h9 y hy]
  refine Hs.last (Hs.ite (t := 5) (show kPair ≠ v1 by decide) (fun he => ?_) (fun he => ?_)) (fun d hd m hm => ⟨hd, by omega⟩)
  · have hp1 : pb = 1 := by simpa [Cnd.eval, pc, cc.one] using he
    refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C t4 t3 c (by decide)) (fun d1 hd1 => ?_)
    subst hd1
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_mul C t3 t4 t0 _ (by decide) (by decide) (by decide) (by
      vsimp [x1]; exact hsq _ hpk)) (fun d2 hd2 => ?_)
    subst hd2
    have hg : groupSize pb ps[k] = ps[k] * ps[k] := by simp [groupSize, hp1]
    refine Hs.mono (hs_add C kG t0 _ (by decide) (by
      simp only [DS.set_env_self, DS.set_env_ne _ _ (show kG ≠ t0 by decide), DS.set_env_ne _ _ (show kG ≠ t4 by decide), DS.set_env_ne _ _ (show t3 ≠ t4 by decide), gc, x1]; omega)) le_rfl ?_
    rintro d rfl
    refine common _ (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; vsimp [hy])
      (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) ?_
    rw [hsum, hg]; simp only [DS.set_env_self, DS.set_env_ne _ _ (show kG ≠ t0 by decide), DS.set_env_ne _ _ (show kG ≠ t4 by decide), DS.set_env_ne _ _ (show t3 ≠ t4 by decide), gc, x1]
  · have hp1 : pb ≠ 1 := by simpa [Cnd.eval, pc, cc.one] using he
    have hg : groupSize pb ps[k] = ps[k] := by simp [groupSize, hp1]
    refine Hs.mono (hs_add C kG t3 c (by decide) (by rw [gc, x1]; omega)) (by norm_num) ?_
    rintro d rfl
    refine common _ (fun y hy => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; vsimp [hy])
      (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) (by vsimp []) ?_
    rw [hsum, hg]; vsimp [x1, gc]

end NearQuarticWires.Reconstruct
