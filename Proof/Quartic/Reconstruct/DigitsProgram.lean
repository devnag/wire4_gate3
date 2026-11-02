import Proof.Quartic.Reconstruct.CopyProgram

/-!
# Reading a digit vector into two record stores

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the digit vector `δ` of a system).

A gathered item carries the digit vector `δ` as `listWord intWord` (`SystemsSplit.gatheredItem`). `digitsS` reads it
and writes the positive parts `max(δ_i, 0)` into the store `sDp` and the negative parts `max(-δ_i, 0)` into the store
`sDn`, from their cursors on (`digitsS_spec`), for Horner's scheme (`Horner.hornerS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)

variable {C : Ctx}

/-- The store of the positive parts of the digits. -/
def sDp : Fin MM := ⟨2, by decide⟩
/-- The store of the negative parts of the digits. -/
def sDn : Fin MM := ⟨3, by decide⟩
/-- The number of digits. -/
def dN : Fin VV := ⟨63, by decide⟩
/-- The digit counter. -/
def dK : Fin VV := ⟨64, by decide⟩
/-- The sign of a digit. -/
def dS : Fin VV := ⟨65, by decide⟩

/-- Read one signed digit and write its two parts. -/
def digitBodyS : St VV MM :=
  .seq rdNatI (.seq (.op (.copy dS t3)) (.seq rdNatI (.ite (.eq dS vZ)
    (.seq (.op (.wrM sDp t3)) (.op (.wrM sDn vZ))) (.seq (.op (.wrM sDp vZ)) (.op (.wrM sDn t3))))))

/-- Read `listWord intWord δ` and write the parts of the digits. -/
def digitsS : St VV MM :=
  .seq rdNatI (.seq (.op (.copy dN t3)) (.seq (.op (.zero dK)) (.loop (.lt dK dN) (.seq digitBodyS (.op (.inc dK))))))

/-- The variables written by `digitsS`. -/
def digitsT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, dN, dK, dS]

/-- The stores hold the parts of the first `k` digits from position `p`. -/
def DigitsIn (b : DS VV MM) (p : ℕ) (ds : List ℤ) (k : ℕ) : Prop :=
  b.rc sDp = p + k ∧ b.rc sDn = p + k ∧ p + k ≤ (b.ram sDp).length ∧ p + k ≤ (b.ram sDn).length ∧
    ∀ i < k, (b.ram sDp).getD (p + i) 0 = (ds.getD i 0).toNat ∧ (b.ram sDn).getD (p + i) 0 = (-(ds.getD i 0)).toNat

theorem putAt_getD_lt (l : List ℕ) (i v j : ℕ) (hi : i ≤ l.length) (hj : j < i) :
    (putAt l i v).getD j 0 = l.getD j 0 := getD_putAt_ne l i v j hi (by omega)

theorem sDp_ne_sDn : sDp ≠ sDn := by decide

/-- Writing the two parts of digit `k` extends the stored digits. -/
theorem digitsIn_put (b : DS VV MM) (p : ℕ) (ds : List ℤ) (k : ℕ) (h : DigitsIn b p ds k) (vp vn : ℕ)
    (hvp : vp = (ds.getD k 0).toNat) (hvn : vn = (-(ds.getD k 0)).toNat) :
    DigitsIn ((b.put sDp vp).put sDn vn) p ds (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hne : sDn ≠ sDp := sDp_ne_sDn.symm
  simp only [DigitsIn, DS.put, Function.update_self, Function.update_of_ne hne,
    Function.update_of_ne sDp_ne_sDn]
  refine ⟨by omega, by omega, ?_, ?_, fun i hi => ?_⟩
  · rw [putAt_length _ _ _ (by omega)]; omega
  · rw [h2, putAt_length _ _ _ (by omega)]; omega
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rw [h1, getD_putAt_ne _ _ _ _ (by omega) (by omega), h2, getD_putAt_ne _ _ _ _ (by omega) (by omega)]
      exact h5 i hi'
    · rw [h1, getD_putAt_self _ _ _ (by omega), h2, getD_putAt_self _ _ _ (by omega)]
      exact ⟨hvp, hvn⟩

/-- The effect of reading digits: the input cursor advances by `k`, the output, the other stores and the call
buffers are unchanged, and only the variables in `digitsT` change. -/
structure DigitsMoved (a b : DS VV MM) (k : ℕ) : Prop where
  ip : b.ip = a.ip + k
  out : b.out = a.out
  ram : ∀ m, m ≠ sDp → m ≠ sDn → b.ram m = a.ram m
  rc : ∀ m, m ≠ sDp → m ≠ sDn → b.rc m = a.rc m
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b digitsT

theorem digitBodyS_spec (b : DS VV MM) (hc : Cst b) (z : ℤ) (rest : List Bool)
    (hin : C.inp.drop b.ip = NearCubicGates.Close.Interfaces.intWord z ++ rest)
    (hW : natBitLength z.natAbs + 2 ≤ C.Wd) (p : ℕ) (ds : List ℤ) (k : ℕ) (hk : ds.getD k 0 = z)
    (hd : DigitsIn b p ds k) :
    Hs C digitBodyS b (60 * C.Wd + 80) (fun c => DigitsIn c p ds (k + 1) ∧
      DigitsMoved b c (NearCubicGates.Close.Interfaces.intWord z).length ∧ Cst c ∧
      c.env dK = b.env dK ∧ c.env dN = b.env dN) := by
  have hW2 : 2 ≤ C.Wd := by have : 1 ≤ natBitLength z.natAbs := by unfold natBitLength; omega
                            omega
  have hsW : natBitLength (if z < 0 then 1 else 0) + 2 ≤ C.Wd := by
    have : natBitLength (if z < 0 then 1 else 0) = 1 := by split <;> simp [natBitLength]
    have : 1 ≤ natBitLength z.natAbs := by unfold natBitLength; omega
    omega
  have hin1 : C.inp.drop b.ip = natWord (if z < 0 then 1 else 0) ++ (natWord z.natAbs ++ rest) := by
    rw [hin]; unfold NearCubicGates.Close.Interfaces.intWord; rw [List.append_assoc]
  refine Hx.hs (Hs.then (rdNatI_spec b hc _ _ hin1 hsW) (fun b1 ⟨r1, _, r3, r4, r5⟩ n1 hn1 => ?_))
  have c1 : Cst b1 := Cst.of_fr hc r5 (by decide)
  refine Hs.then (hs_copy C dS t3 b1 (by decide)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  have c2 : Cst (b1.set dS (b1.env t3)) := ⟨by vsimp [c1.z], by vsimp [c1.one], by vsimp [c1.two]⟩
  have hin2 : C.inp.drop (b1.set dS (b1.env t3)).ip = natWord z.natAbs ++ rest := by
    show C.inp.drop b1.ip = _
    rw [r3, ← List.drop_drop, hin1, List.drop_left]
  refine Hs.then (rdNatI_spec _ c2 _ _ hin2 (by omega)) (fun b3 ⟨s1, _, s3, s4, s5⟩ n3 hn3 => ?_)
  have c3 : Cst b3 := Cst.of_fr c2 s5 (by decide)
  have b3S : b3.env dS = if z < 0 then 1 else 0 := by
    rw [s5 dS (by decide)]; vsimp [r1]
  simp only [Prod.mk.injEq] at r4 s4
  obtain ⟨o1, m1, q1, i1, k1, kc1⟩ := r4
  obtain ⟨o3, m3, q3, i3, k3, kc3⟩ := s4
  have hd3 : DigitsIn b3 p ds k := by
    obtain ⟨d1, d2, d3, d4, d5⟩ := hd
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [q3]; show b1.rc sDp = _; rw [q1, d1]
    · rw [q3]; show b1.rc sDn = _; rw [q1, d2]
    · rw [m3]; show _ ≤ (b1.ram sDp).length; rw [m1]; exact d3
    · rw [m3]; show _ ≤ (b1.ram sDn).length; rw [m1]; exact d4
    · intro i hi; rw [m3]; show _ ∧ _; simp only [DS.set_ram]; rw [m1]; exact d5 i hi
  have hmoved : ∀ (c : DS VV MM), c.ip = b3.ip → c.out = b3.out → (∀ m, m ≠ sDp → m ≠ sDn → c.ram m = b3.ram m) →
      (∀ m, m ≠ sDp → m ≠ sDn → c.rc m = b3.rc m) → c.kin = b3.kin → c.kout = b3.kout → c.kc = b3.kc →
      Fr b3 c digitsT → DigitsMoved b c (NearCubicGates.Close.Interfaces.intWord z).length := by
    intro c e1 e2 e3 e4 e5 e6 e7 e8
    refine ⟨?_, ?_, fun m h1 h2 => ?_, fun m h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1, s3]; show b1.ip + _ = _; rw [r3]
      unfold NearCubicGates.Close.Interfaces.intWord; rw [List.length_append]; ring
    · rw [e2, o3]; exact o1
    · rw [e3 m h1 h2, m3]; show b1.ram m = _; rw [m1]
    · rw [e4 m h1 h2, q3]; show b1.rc m = _; rw [q1]
    · rw [e5, i3]; exact i1
    · rw [e6, k3]; exact k1
    · rw [e7, kc3]; exact kc1
    · exact Fr.trans (Fr.trans (r5.weaken (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (s5.weaken (by decide))))
        e8
  have hrc3 : b3.rc sDp ≤ (b3.ram sDp).length := by rw [hd3.1]; exact hd3.2.2.1
  have b3K : b3.env dK = b.env dK := by rw [s5 dK (by decide)]; vsimp [r5 dK (by decide)]
  have b3N : b3.env dN = b.env dN := by rw [s5 dN (by decide)]; vsimp [r5 dN (by decide)]
  refine Hs.last (Hs.ite (c := .eq dS vZ) (t := 3) (show dS ≠ vZ by decide) (fun he => ?_) (fun he => ?_))
    (fun c hc' n hn => ⟨hc', by omega⟩)
  · have hz : ¬ z < 0 := by
      intro h; simp [Cnd.eval, b3S, c3.z, h] at he
    have e3 : b3.env t3 = z.natAbs := s1
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C sDp t3 b3 hrc3) (fun c1' hc1 => ?_)
    subst hc1
    have hrc4 : (b3.put sDp (b3.env t3)).rc sDn ≤ ((b3.put sDp (b3.env t3)).ram sDn).length := by
      simp only [DS.put, Function.update_of_ne sDp_ne_sDn.symm]
      rw [hd3.2.1]; exact hd3.2.2.2.1
    refine Hs.mono (hs_wrM C sDn vZ _ hrc4) le_rfl ?_
    rintro c rfl
    refine ⟨digitsIn_put b3 p ds k hd3 _ _ (by rw [e3, hk]; omega) (by simp only [DS.put]; rw [c3.z, hk]; omega), ?_,
      ⟨by simp [DS.put, c3.z], by simp [DS.put, c3.one], by simp [DS.put, c3.two]⟩, by simp [DS.put, b3K],
      by simp [DS.put, b3N]⟩
    refine hmoved _ rfl rfl (fun m h1 h2 => ?_) (fun m h1 h2 => ?_) rfl rfl rfl (fun y _ => rfl)
    · simp [DS.put, Function.update_of_ne h1, Function.update_of_ne h2]
    · simp [DS.put, Function.update_of_ne h1, Function.update_of_ne h2]
  · have hz : z < 0 := by
      by_contra h; simp [Cnd.eval, b3S, c3.z, h] at he
    have e3 : b3.env t3 = z.natAbs := s1
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C sDp vZ b3 hrc3) (fun c1' hc1 => ?_)
    subst hc1
    have hrc4 : (b3.put sDp (b3.env vZ)).rc sDn ≤ ((b3.put sDp (b3.env vZ)).ram sDn).length := by
      simp only [DS.put, Function.update_of_ne sDp_ne_sDn.symm]
      rw [hd3.2.1]; exact hd3.2.2.2.1
    refine Hs.mono (hs_wrM C sDn t3 _ hrc4) le_rfl ?_
    rintro c rfl
    refine ⟨digitsIn_put b3 p ds k hd3 _ _ (by rw [c3.z, hk]; omega) (by simp only [DS.put]; rw [e3, hk]; omega), ?_,
      ⟨by simp [DS.put, c3.z], by simp [DS.put, c3.one], by simp [DS.put, c3.two]⟩, by simp [DS.put, b3K],
      by simp [DS.put, b3N]⟩
    refine hmoved _ rfl rfl (fun m h1 h2 => ?_) (fun m h1 h2 => ?_) rfl rfl rfl (fun y _ => rfl)
    · simp [DS.put, Function.update_of_ne h1, Function.update_of_ne h2]
    · simp [DS.put, Function.update_of_ne h1, Function.update_of_ne h2]

theorem DigitsMoved.trans {a b c : DS VV MM} {k k' : ℕ} (h1 : DigitsMoved a b k) (h2 : DigitsMoved b c k') :
    DigitsMoved a c (k + k') :=
  ⟨by rw [h2.ip, h1.ip, Nat.add_assoc], h2.out.trans h1.out, fun m p1 p2 => (h2.ram m p1 p2).trans (h1.ram m p1 p2),
    fun m p1 p2 => (h2.rc m p1 p2).trans (h1.rc m p1 p2), h2.kin.trans h1.kin, h2.kout.trans h1.kout,
    h2.kc.trans h1.kc, Fr.trans h1.fr h2.fr⟩

theorem DigitsMoved.set {a b : DS VV MM} {k : ℕ} (h : DigitsMoved a b k) {x : Fin VV} (v : ℕ) (hx : x ∈ digitsT) :
    DigitsMoved a (b.set x v) k :=
  ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx)⟩

/-- **Reading a digit vector.** From `listWord intWord δ` on the input and the two stores at a common cursor `p`,
`digitsS` writes the positive and the negative parts of the digits at positions `p, p + 1, …`. -/
theorem digitsS_spec (a : DS VV MM) (hc : Cst a) (ds : List ℤ) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord NearCubicGates.Close.Interfaces.intWord ds ++ rest)
    (hW : ∀ z ∈ ds, natBitLength z.natAbs + 2 ≤ C.Wd) (hWl : natBitLength ds.length + 2 ≤ C.Wd)
    (p : ℕ) (hd : DigitsIn a p ds 0) :
    Hs C digitsS a (ds.length * (60 * C.Wd + 84) + 40 * C.Wd + 40)
      (fun b => DigitsIn b p ds ds.length ∧
        DigitsMoved a b (listWord NearCubicGates.Close.Interfaces.intWord ds).length ∧ Cst b) := by
  have hW1 : 1 ≤ natBitLength ds.length := by unfold natBitLength; omega
  have hin0 : C.inp.drop a.ip = natWord ds.length ++ (ds.flatMap NearCubicGates.Close.Interfaces.intWord ++ rest) := by
    rw [hin]; unfold listWord; rw [List.append_assoc]
  have hlenW : ds.length < 2 ^ C.Wd := lt_of_lt_of_le (lt_natBitLength _)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hx.hs (Hs.then (rdNatI_spec a hc _ _ hin0 hWl) (fun b0 ⟨r1, _, r3, r4, r5⟩ n0 hn0 => ?_))
  have c0 : Cst b0 := Cst.of_fr hc r5 (by decide)
  simp only [Prod.mk.injEq] at r4
  obtain ⟨o0, m0, q0, i0, k0, kc0⟩ := r4
  have m0' : DigitsMoved a b0 (natWord ds.length).length :=
    ⟨r3, o0, fun m _ _ => by rw [m0], fun m _ _ => by rw [q0], i0, k0, kc0, r5.weaken (by decide)⟩
  have hd0 : DigitsIn b0 p ds 0 := by
    obtain ⟨d1, d2, d3, d4, _⟩ := hd
    exact ⟨by rw [q0, d1], by rw [q0, d2], by rw [m0]; exact d3, by rw [m0]; exact d4, fun i hi => absurd hi (by omega)⟩
  refine Hs.then (hs_copy C dN t3 b0 (by decide)) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_zero C dK _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  set b2 := (b0.set dN (b0.env t3)).set dK 0 with hb2def
  have hT : dN ∈ digitsT ∧ dK ∈ digitsT := by decide
  let I : ℕ → DS VV MM → Prop := fun k b => b.env dK = k ∧ b.env dN = ds.length ∧ DigitsIn b p ds k ∧
    DigitsMoved a b ((natWord ds.length).length + ((ds.take k).flatMap NearCubicGates.Close.Interfaces.intWord).length) ∧
    Cst b
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt dK dN) (.seq digitBodyS (.op (.inc dK)))) b
      (ds.length * ((60 * C.Wd + 80 + 2) + 2) + 2) (I ds.length) := by
    refine Hs.loopN (c := .lt dK dN) (show dK ≠ dN by decide) I ds.length (60 * C.Wd + 80 + 2) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5⟩
      refine ⟨by simp only [Cnd.eval, h1, h2, decide_eq_true_eq]; exact hk, ?_⟩
      have e1 : ds.flatMap NearCubicGates.Close.Interfaces.intWord ++ rest =
          (ds.take k).flatMap NearCubicGates.Close.Interfaces.intWord ++
            ((ds.drop k).flatMap NearCubicGates.Close.Interfaces.intWord ++ rest) := by
        rw [← List.append_assoc, ← List.flatMap_append, List.take_append_drop]
      have hinb : C.inp.drop b.ip = NearCubicGates.Close.Interfaces.intWord ds[k] ++
          ((ds.drop (k + 1)).flatMap NearCubicGates.Close.Interfaces.intWord ++ rest) := by
        rw [h4.ip, ← List.drop_drop, hin0, ← List.drop_drop, List.drop_left, e1, List.drop_left,
          List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
      have hgk : ds.getD k 0 = ds[k] := by rw [List.getD_eq_getElem _ _ hk]
      refine Hs.seq (t1 := 60 * C.Wd + 80) (t2 := 1)
        (digitBodyS_spec b h5 ds[k] _ hinb (hW _ (List.getElem_mem hk)) p ds k hgk h3)
        (fun e ⟨e1', e2', e3', e4', e5'⟩ => ?_)
      have eK : e.env dK = k := by rw [e4', h1]
      have eN : e.env dN = ds.length := by rw [e5', h2]
      refine Hs.mono (hs_inc C dK e (by rw [eK]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨by vsimp [eK], by vsimp [eN], ?_, ?_, ⟨by vsimp [e3'.z], by vsimp [e3'.one], by vsimp [e3'.two]⟩⟩
      · obtain ⟨d1, d2, d3, d4, d5⟩ := e1'
        exact ⟨d1, d2, d3, d4, d5⟩
      · have hm := (h4.trans e2').set (e.env dK + 1) hT.2
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton, List.length_append,
          ← Nat.add_assoc]
        exact hm
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  refine Hs.last (loop b2 ⟨by vsimp [hb2def], by vsimp [hb2def, r1], ?_, ?_, ?_⟩) (fun b hb n hn => ?_)
  · obtain ⟨d1, d2, d3, d4, d5⟩ := hd0
    exact ⟨d1, d2, d3, d4, d5⟩
  · simpa using (m0'.set _ hT.1).set 0 hT.2
  · exact ⟨by vsimp [hb2def, c0.z], by vsimp [hb2def, c0.one], by vsimp [hb2def, c0.two]⟩
  · obtain ⟨_, _, h3, h4, h5⟩ := hb
    refine ⟨⟨h3, ?_, h5⟩, ?_⟩
    · rw [List.take_length] at h4
      unfold listWord
      rw [List.length_append]
      exact h4
    · have : ds.length * (60 * C.Wd + 80 + 2 + 2) = ds.length * (60 * C.Wd + 84) := by ring
      have hlb : natBitLength ds.length ≤ C.Wd := by omega
      omega

end NearQuarticWires.Reconstruct
