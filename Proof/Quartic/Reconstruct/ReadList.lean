import Proof.Quartic.Reconstruct.AxisOne

/-!
# Reading a list of numbers into a record store

`readListS m` reads `listWord natWord vs` from the input into the empty record store `m` (`readListS_spec`): the
parameter reading of the stage stores the rates (the factor list of `parametersWord`) this way.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)

variable {C : Ctx}

/-- The number of numbers to read. -/
def lN : Fin VV := ⟨77, by decide⟩
/-- The counter of the read numbers. -/
def lK : Fin VV := ⟨78, by decide⟩

/-- Read `listWord natWord vs` into store `m`. -/
def readListS (m : Fin MM) : St VV MM :=
  .seq rdNatI (.seq (.op (.copy lN t3)) (.seq (.op (.zero lK))
    (.loop (.lt lK lN) (.seq rdNatI (.seq (.op (.wrM m t3)) (.op (.inc lK)))))))

/-- The variables written by `readListS`. -/
def readListT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, lN, lK]

theorem readListS_spec (m : Fin MM) (a : DS VV MM) (hc : Cst a) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord natWord vs ++ rest) (hm : a.ram m = []) (hrc : a.rc m = 0) (ℓ : ℕ)
    (hW : ∀ v ∈ vs.length :: vs, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (readListS m) a (vs.length * (30 * ℓ + 36) + 30 * ℓ + 40)
      (fun b => b.ram m = vs ∧ b.rc m = vs.length ∧ b.ip = a.ip + (listWord natWord vs).length ∧ b.out = a.out ∧
        (∀ m', m' ≠ m → b.ram m' = a.ram m' ∧ b.rc m' = a.rc m') ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
        b.kc = a.kc ∧ Fr a b readListT ∧ Cst b) := by
  have hl0 : natBitLength vs.length ≤ ℓ := hW _ (by simp)
  have hvs : ∀ v ∈ vs, natBitLength v ≤ ℓ := fun v hv => hW v (List.mem_cons_of_mem _ hv)
  have hlenW : vs.length < 2 ^ C.Wd := lt_of_lt_of_le (lt_natBitLength _)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hin0 : C.inp.drop a.ip = natWord vs.length ++ (vs.flatMap natWord ++ rest) := by
    rw [hin]; unfold listWord; rw [List.append_assoc]
  refine Hx.hs (Hs.then (rdNatI_spec a hc _ _ hin0 (by omega)) (fun b0 ⟨r1, _, r3, r4, r5⟩ n0 hn0 => ?_))
  have c0 : Cst b0 := Cst.of_fr hc r5 (by decide)
  simp only [Prod.mk.injEq] at r4
  obtain ⟨o0, m0, q0, i0, k0, kc0⟩ := r4
  refine Hs.then (hs_copy C lN t3 b0 (by decide)) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_zero C lK _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  set b2 := (b0.set lN (b0.env t3)).set lK 0 with hb2def
  let I : ℕ → DS VV MM → Prop := fun k b => b.env lK = k ∧ b.env lN = vs.length ∧ b.ram m = vs.take k ∧
    b.rc m = k ∧ b.ip = a.ip + (natWord vs.length).length + ((vs.take k).flatMap natWord).length ∧
    b.out = a.out ∧ (∀ m', m' ≠ m → b.ram m' = a.ram m' ∧ b.rc m' = a.rc m') ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
    b.kc = a.kc ∧ Fr a b readListT ∧ Cst b
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt lK lN) (.seq rdNatI (.seq (.op (.wrM m t3)) (.op (.inc lK))))) b
      (vs.length * ((30 * ℓ + 34) + 2) + 2) (I vs.length) := by
    refine Hs.loopN (c := .lt lK lN) (show lK ≠ lN by decide) I vs.length (30 * ℓ + 34) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
      refine ⟨by simp only [Cnd.eval, h1, h2, decide_eq_true_eq]; exact hk, ?_⟩
      have e1 : vs.flatMap natWord ++ rest = (vs.take k).flatMap natWord ++ ((vs.drop k).flatMap natWord ++ rest) := by
        rw [← List.append_assoc, ← List.flatMap_append, List.take_append_drop]
      have hinb : C.inp.drop b.ip = natWord vs[k] ++ ((vs.drop (k + 1)).flatMap natWord ++ rest) := by
        rw [h5, ← List.drop_drop, ← List.drop_drop, hin0, List.drop_left, e1, List.drop_left,
          List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
      have hvk : natBitLength vs[k] ≤ ℓ := hvs _ (List.getElem_mem hk)
      refine Hs.seq (t1 := 30 * natBitLength vs[k] + 30) (t2 := 3) (rdNatI_spec b h12 _ _ hinb (by omega))
        (fun e ⟨s1, _, s3, s4, s5⟩ => ?_) |>.mono (by omega) (fun _ h => h)
      simp only [Prod.mk.injEq] at s4
      obtain ⟨o1, m1, q1, i1, k1, kc1⟩ := s4
      have hrcm : e.rc m ≤ (e.ram m).length := by rw [q1, m1, h4, h3]; simp; omega
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C m t3 e hrcm) (fun f hf => ?_)
      subst hf
      have eK : (e.put m (e.env t3)).env lK = k := by
        simp only [DS.put]; rw [s5 lK (by decide), h1]
      refine Hs.mono (hs_inc C lK _ (by rw [eK]; omega)) le_rfl ?_
      rintro g rfl
      have hput : (e.put m (e.env t3)).ram m = vs.take (k + 1) := by
        simp only [DS.put, Function.update_self]
        rw [q1, h4, m1, h3, s1]
        unfold putAt
        rw [if_neg (by simp), List.take_succ_eq_append_getElem hk]
      refine ⟨by vsimp [eK], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ (by decide)]; simp only [DS.put]; rw [s5 lN (by decide), h2]
      · simp only [DS.set_ram]; exact hput
      · simp only [DS.set_rc, DS.put, Function.update_self]; rw [q1, h4]
      · simp only [DS.set_ip, DS.put]
        rw [s3, h5, List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton,
          List.length_append]
        ring
      · simp only [DS.set_out, DS.put]; rw [o1, h6]
      · intro m' hm'
        simp only [DS.set_ram, DS.set_rc, DS.put, Function.update_of_ne hm']
        rw [m1, q1]; exact h7 m' hm'
      · simp only [DS.set_kin, DS.put]; rw [i1, h8]
      · simp only [DS.set_kout, DS.put]; rw [k1, h9]
      · simp only [DS.set_kc, DS.put]; rw [kc1, h10]
      · exact Fr.trans h11 (Fr.trans (s5.weaken (by decide)) (fun y hy => by
          simp only [DS.put]; exact DS.set_env_ne _ _ (fun h => hy (by rw [h]; decide))))
      · exact ⟨by vsimp [DS.put]; rw [s5 vZ (by decide)]; exact h12.z,
          by vsimp [DS.put]; rw [s5 v1 (by decide)]; exact h12.one,
          by vsimp [DS.put]; rw [s5 v2 (by decide)]; exact h12.two⟩
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  refine Hs.last (loop b2 ⟨by vsimp [hb2def], by vsimp [hb2def, r1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    (fun b hb n hn => ?_)
  · simp only [hb2def, DS.set_ram]; rw [m0, hm]; simp
  · simp only [hb2def, DS.set_rc]; rw [q0, hrc]
  · simp only [hb2def, DS.set_ip]; rw [r3]; simp
  · simp only [hb2def, DS.set_out]; rw [o0]
  · intro m' _; simp only [hb2def, DS.set_ram, DS.set_rc]; rw [m0, q0]; exact ⟨rfl, rfl⟩
  · simp only [hb2def, DS.set_kin]; rw [i0]
  · simp only [hb2def, DS.set_kout]; rw [k0]
  · simp only [hb2def, DS.set_kc]; rw [kc0]
  · exact Fr.trans (r5.weaken (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
  · exact ⟨by vsimp [hb2def, c0.z], by vsimp [hb2def, c0.one], by vsimp [hb2def, c0.two]⟩
  · obtain ⟨_, _, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hb
    rw [List.take_length] at h3 h5
    refine ⟨⟨h3, h4, ?_, h6, h7, h8, h9, h10, h11, h12⟩, ?_⟩
    · rw [h5]; unfold listWord; rw [List.length_append]; ring
    · have : vs.length * (30 * ℓ + 34 + 2) = vs.length * (30 * ℓ + 36) := by ring
      omega

/-! ## Skipping numbers -/

/-- Read `k` numbers, keeping none (`k` fixed in the program). -/
def skipNatsS : ℕ → St VV MM
  | 0 => skipS
  | k + 1 => .seq rdNatI (skipNatsS k)

/-- **Skipping numbers.** -/
theorem skipNatsS_spec (vs : List ℕ) (a : DS VV MM) (hc : Cst a) (rest : List Bool)
    (hin : C.inp.drop a.ip = vs.flatMap natWord ++ rest) (ℓ : ℕ) (hW : ∀ v ∈ vs, natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (skipNatsS vs.length) a (vs.length * (30 * ℓ + 31) + 1)
      (fun b => b.ip = a.ip + (vs.flatMap natWord).length ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b rdNatT ∧ Cst b) := by
  induction vs generalizing a with
  | nil =>
    refine Hs.mono (skip_spec a) (by simp) ?_
    rintro b rfl
    exact ⟨by simp, rfl, rfl, rfl, rfl, rfl, rfl, Fr.set a 0 (by decide),
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩
  | cons v vs ih =>
    have hv : natBitLength v ≤ ℓ := hW v (by simp)
    have hin1 : C.inp.drop a.ip = natWord v ++ (vs.flatMap natWord ++ rest) := by
      rw [hin, List.flatMap_cons, List.append_assoc]
    refine Hs.mono (Hs.seq (t1 := 30 * natBitLength v + 30) (t2 := vs.length * (30 * ℓ + 31) + 1)
      (rdNatI_spec a hc v _ hin1 (by omega)) (fun b ⟨_, _, r3, r4, r5⟩ => ?_)) (by simp; nlinarith)
      (fun _ h => h)
    have cb : Cst b := Cst.of_fr hc r5 (by decide)
    have hinb : C.inp.drop b.ip = vs.flatMap natWord ++ rest := by
      rw [r3, ← List.drop_drop, hin1, List.drop_left]
    refine (ih b cb hinb (fun w hw => hW w (by simp [hw]))).mono le_rfl ?_
    rintro c ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩
    simp only [Prod.mk.injEq] at r4
    obtain ⟨o, m, q, i, k, kc⟩ := r4
    refine ⟨?_, c2.trans o, c3.trans m, c4.trans q, c5.trans i, c6.trans k, c7.trans kc, Fr.trans r5 c8, c9⟩
    rw [c1, r3, List.flatMap_cons, List.length_append]
    ring

end NearQuarticWires.Reconstruct
