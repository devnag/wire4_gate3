import Proof.Quartic.Reconstruct.GatherProgStep
import Proof.Gates.CounterMachine.PrefixRun

/-!
# The gathering program: the context and the groups

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`ctxS` copies the context (every field a number) and keeps the number `tg` of tables per group, the certified bits
(store `sZc`) and their number `n_c` (`ctxS_spec`). `headG` reads the number `m` of tables and writes the number
`(m / tg / 2)·n_c` of listed systems; `groupsS` runs `groupS` on every group (`groupsS_spec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.Reconstruct

variable {C : Ctx}

/-! ## Copying numbers -/

/-- Copy `k` numbers. -/
def copyN : ℕ → St VV MM
  | 0 => skipS
  | k + 1 => .seq (copyNatS 1) (copyN k)

theorem copyCost_mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') : copyCost 1 ℓ ≤ copyCost 1 ℓ' := by
  unfold copyCost; rw [emitNatDCost_one, emitNatDCost_one]; omega

theorem copyN_spec (vs : List ℕ) (a : DS VV MM) (hc : Cst a) (rest : List Bool)
    (hin : C.inp.drop a.ip = vs.flatMap natWord ++ rest) (ℓ : ℕ) (hv : ∀ v ∈ vs, natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (copyN vs.length) a (vs.length * (copyCost 1 ℓ + 1) + 1)
      (fun b => Ran a b (vs.flatMap natWord).length (marksD 1 (vs.flatMap natWord)) copyT [] ∧ Cst b ∧
        C.inp.drop b.ip = rest) := by
  induction vs generalizing a with
  | nil =>
    refine (skip_spec a).mono (by simp) ?_
    rintro b rfl
    exact ⟨((Ran.refl a copyT []).set 0 (by decide)).eqk rfl (by simp [marksD]), cst_set hc _ (by decide),
      by simpa using hin⟩
  | cons v vs ih =>
    have hin1 : C.inp.drop a.ip = natWord v ++ (vs.flatMap natWord ++ rest) := by
      rw [hin, List.flatMap_cons, List.append_assoc]
    refine (Hs.seq (t1 := copyCost 1 ℓ) (t2 := vs.length * (copyCost 1 ℓ + 1) + 1)
      ((copyNatS_spec 1 a hc v _ hin1 (by have := hv v (by simp); omega)).mono
        (copyCost_mono (hv v (by simp))) (fun _ h => h)) (fun b ⟨m1, c1, _⟩ => ?_)).mono
      (by simp only [List.length_cons]; ring_nf; omega) (fun _ h => h)
    refine (ih b c1 (by rw [m1.ip]; exact drop_step hin1) (fun w hw => hv w (List.mem_cons_of_mem _ hw))).mono
      le_rfl ?_
    rintro d ⟨r2, c2, i2⟩
    refine ⟨((Ran.of_moved m1 []).trans r2).eqk (by simp) (by simp [marksD_append]), c2, i2⟩

/-! ## The certified bits -/

/-- Copy `gN` bits, storing them in `sZc` and adding them into `gCC`. -/
def certS : St VV MM := .seq (.op (.zero gCC)) (.seq (.op (.zero gK)) (.loop (.lt gK gN) (.seq (copyNatS 1)
  (.seq (.op (.wrM sZc t3)) (.seq (.op (.add gCC t3)) (.op (.inc gK)))))))

/-- The variables written by `certS`. -/
def certT : List (Fin VV) := gCC :: gK :: copyT

theorem certS_spec (a : DS VV MM) (hc : Cst a) (bits vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (bits ++ vs).flatMap natWord ++ rest) (hN : a.env gN = bits.length)
    (hZ : a.ram sZc = []) (hZc : a.rc sZc = 0) (ℓ : ℕ) (hv : ∀ v ∈ bits, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hs : bits.sum + bits.length < 2 ^ C.Wd) :
    Hs C certS a (bits.length * (copyCost 1 ℓ + 9) + 6)
      (fun b => Ran a b (bits.flatMap natWord).length (marksD 1 (bits.flatMap natWord)) certT [sZc] ∧
        b.env gCC = bits.sum ∧ b.ram sZc = bits ∧ b.rc sZc = bits.length ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gK = k ∧ b.env gN = bits.length ∧ b.env gCC = (bits.take k).sum ∧
    b.ram sZc = bits.take k ∧ b.rc sZc = k ∧
    Ran a b ((bits.take k).flatMap natWord).length (marksD 1 ((bits.take k).flatMap natWord)) certT [sZc] ∧ Cst b ∧
    C.inp.drop b.ip = (bits.drop k ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) gK gN (by decide) (.seq (copyNatS 1) (.seq (.op (.wrM sZc t3))
    (.seq (.op (.add gCC t3)) (.op (.inc gK))))) bits.length (copyCost 1 ℓ + 7) I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      have hk' : bits.drop k = bits[k] :: bits.drop (k + 1) := List.drop_eq_getElem_cons hk
      have hin1 : C.inp.drop b.ip = natWord bits[k] ++ ((bits.drop (k + 1) ++ vs).flatMap natWord ++ rest) := by
        rw [h8, hk', List.cons_append, List.flatMap_cons, List.append_assoc]
      have hvk : natBitLength bits[k] ≤ ℓ := hv _ (List.getElem_mem hk)
      have hsum : (bits.take (k + 1)).sum = (bits.take k).sum + bits[k] := by
        rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      have hsle : (bits.take (k + 1)).sum ≤ bits.sum := List.Sublist.sum_le_sum (List.take_sublist _ _)
        (fun _ _ => Nat.zero_le _)
      refine (Hs.seq (t1 := copyCost 1 ℓ) (t2 := 5) ((copyNatS_spec 1 b h7 bits[k] _ hin1 (by omega)).mono
        (copyCost_mono hvk) (fun _ h => h)) (fun d1 ⟨m1, c1, t1⟩ => ?_)).mono (by omega) (fun _ h => h)
      have d1Z : d1.ram sZc = bits.take k ∧ d1.rc sZc = k := ⟨by rw [m1.ram, h4], by rw [m1.rc, h5]⟩
      refine (Hs.seq (t1 := 1) (t2 := 3) (hs_wrM C sZc t3 d1 (by rw [d1Z.1, d1Z.2]; simp; omega))
        (fun d2 hd2 => ?_)).mono (by omega) (fun _ h => h)
      subst hd2
      have d2C : (d1.put sZc (d1.env t3)).env gCC = (bits.take k).sum := by
        rw [DS.put_env, m1.fr gCC (by decide), h3]
      refine (Hs.seq (t1 := 1) (t2 := 1) (hs_add C gCC t3 _ (by decide) (by
        rw [d2C, DS.put_env, t1]; omega)) (fun d3 hd3 => ?_)).mono (by omega) (fun _ h => h)
      subst hd3
      have d3K : ((d1.put sZc (d1.env t3)).set gCC ((d1.put sZc (d1.env t3)).env gCC +
          (d1.put sZc (d1.env t3)).env t3)).env gK = k := by
        rw [DS.set_env_ne _ _ (show gK ≠ gCC by decide), DS.put_env, m1.fr gK (by decide), h1]
      refine Hs.mono (hs_inc C gK _ (by rw [d3K]; omega)) le_rfl ?_
      rintro d4 rfl
      refine ⟨by rw [DS.set_env_self, d3K], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ (show gN ≠ gK by decide), DS.set_env_ne _ _ (show gN ≠ gCC by decide), DS.put_env,
          m1.fr gN (by decide), h2]
      · rw [DS.set_env_ne _ _ (show gCC ≠ gK by decide), DS.set_env_self, d2C, DS.put_env, t1, hsum]
      · rw [DS.set_ram, DS.set_ram, DS.put_ram_self, d1Z.1, d1Z.2, t1, List.take_succ_eq_append_getElem hk]
        have := putAt_ovw [] (bits.take k) bits[k]
        rw [ovw_of_le _ _ (by simp), ovw_of_le _ _ (by simp), List.length_take, Nat.min_eq_left hk.le] at this
        exact this
      · rw [DS.set_rc, DS.set_rc, DS.put_rc_self, d1Z.2]
      · rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton, List.length_append,
          marksD_append]
        exact (((h6.trans ((Ran.of_moved m1 [sZc]).weaken (fun y hy => List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hy)) (fun _ h => h))).put (m := sZc) _ (by simp)).set _ (by decide)).set _
          (by decide)
      · exact cst_set (cst_set (cst_put c1 _ _) _ (by decide)) _ (by decide)
      · rw [DS.set_ip, DS.set_ip, DS.put_ip, m1.ip]; exact drop_step hin1)
  refine Hx.hs (Hs.then (hs_zero C gCC a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C gK _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hN], by vsimp [], by simp [hZ], by simp [hZc],
    (((Ran.refl a certT [sZc]).set (x := gCC) 0 (by decide)).set (x := gK) 0 (by decide)).eqk (by simp)
      (by simp [marksD]), cst_set (cst_set hc _ (by decide)) _ (by decide), by simpa using hin⟩)
    (fun b ⟨_, _, h3, h4, h5, h6, h7, h8⟩ n hn => ⟨⟨?_, by rw [h3, List.take_length], by rw [h4, List.take_length],
      h5, h7, by simpa using h8⟩, ?_⟩)
  · rw [List.take_length] at h6; exact h6
  · have e : bits.length * (copyCost 1 ℓ + 7 + 2) = bits.length * (copyCost 1 ℓ + 9) := by ring
    omega

/-! ## The context -/

/-- Copy the context, keeping `tg` in `gTG`, the certified bits in `sZc` and their sum in `gCC`. -/
def ctxS : St VV MM := .seq (copyN 5) (.seq (copyNatS 1) (.seq (.op (.copy cN t3)) (.seq (copyNatsS 1)
  (.seq (copyN 4) (.seq (copyNatS 1) (.seq (.op (.copy gTG t3)) (.seq (copyNatS 1) (.seq (.op (.copy gN t3))
    certS))))))))

/-- The numbers of the context. -/
def ctxNats (pre5 fs mid4 : List ℕ) (tg : ℕ) (bits : List ℕ) : List ℕ :=
  pre5 ++ [fs.length] ++ fs ++ mid4 ++ [tg, bits.length] ++ bits

/-- The variables written by `ctxS`. -/
def ctxT : List (Fin VV) := [gTG, gN, cN, cK, gCC, gK] ++ copyT

/-- The cost of `ctxS`. -/
def ctxCost (ℓ nf nb : ℕ) : ℕ := (nf + nb + 20) * (copyCost 1 ℓ + 9)

theorem ctxS_spec (a : DS VV MM) (hc : Cst a) (pre5 fs mid4 : List ℕ) (h5 : pre5.length = 5)
    (h4 : mid4.length = 4) (tg : ℕ) (bits vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (ctxNats pre5 fs mid4 tg bits ++ vs).flatMap natWord ++ rest)
    (hZ : a.ram sZc = []) (hZc : a.rc sZc = 0) (ℓ : ℕ) (hv : ∀ v ∈ ctxNats pre5 fs mid4 tg bits, natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) (hs : bits.sum + bits.length < 2 ^ C.Wd) (hfs : fs.length < 2 ^ C.Wd) :
    Hs C ctxS a (ctxCost ℓ fs.length bits.length)
      (fun b => Ran a b ((ctxNats pre5 fs mid4 tg bits).flatMap natWord).length
        (marksD 1 ((ctxNats pre5 fs mid4 tg bits).flatMap natWord)) ctxT [sZc] ∧ b.env gTG = tg ∧
        b.env gCC = bits.sum ∧ b.ram sZc = bits ∧ b.rc sZc = bits.length ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have mem : ∀ v, v ∈ ctxNats pre5 fs mid4 tg bits → natBitLength v ≤ ℓ := hv
  have hin1 : C.inp.drop a.ip = pre5.flatMap natWord ++ ((fs.length :: (fs ++ (mid4 ++ (tg :: bits.length ::
      (bits ++ vs))))).flatMap natWord ++ rest) := by
    rw [hin]; simp [ctxNats, List.append_assoc]
  have wC : ∀ y ∈ copyT, y ∈ ctxT := fun y hy => by revert y; decide
  have wS : ∀ m ∈ ([] : List (Fin MM)), m ∈ [sZc] := fun _ h => by simp at h
  refine Hx.hs (Hs.then (h5 ▸ copyN_spec pre5 a hc _ hin1 ℓ (fun v h => mem v (by simp [ctxNats, h])) hℓ)
    (fun b1 ⟨r1, c1, i1⟩ n1 hn1 => ?_))
  have i1' : C.inp.drop b1.ip = natWord fs.length ++ ((fs ++ (mid4 ++ (tg :: bits.length :: (bits ++ vs)))).flatMap
      natWord ++ rest) := by rw [i1, List.flatMap_cons, List.append_assoc]
  refine Hs.then (copyNatS_spec 1 b1 c1 fs.length _ i1' (by have := mem fs.length (by simp [ctxNats]); omega))
    (fun b2 ⟨m2, c2, t2⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C cN t3 b2 (by decide)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  have i3 : C.inp.drop (b2.set cN (b2.env t3)).ip = fs.flatMap natWord ++ ((mid4 ++ (tg :: bits.length ::
      (bits ++ vs))).flatMap natWord ++ rest) := by
    rw [DS.set_ip, m2.ip, drop_step i1', List.flatMap_append, List.append_assoc]
  refine Hs.then (copyNatsS_spec 1 ℓ _ (cst_set c2 _ (by decide)) fs _ i3 (by rw [DS.set_env_self, t2])
    (fun v h => mem v (by simp [ctxNats, h])) hℓ hfs) (fun b4 ⟨m4, c4⟩ n4 hn4 => ?_)
  have i4 : C.inp.drop b4.ip = mid4.flatMap natWord ++ ((tg :: bits.length :: (bits ++ vs)).flatMap natWord ++
      rest) := by
    rw [m4.ip, drop_step i3, List.flatMap_append, List.append_assoc]
  refine Hs.then (h4 ▸ copyN_spec mid4 b4 c4 _ i4 ℓ (fun v h => mem v (by simp [ctxNats, h])) hℓ)
    (fun b5 ⟨r5, c5, i5⟩ n5 hn5 => ?_)
  have i5' : C.inp.drop b5.ip = natWord tg ++ ((bits.length :: (bits ++ vs)).flatMap natWord ++ rest) := by
    rw [i5, List.flatMap_cons, List.append_assoc]
  refine Hs.then (copyNatS_spec 1 b5 c5 tg _ i5' (by have := mem tg (by simp [ctxNats]); omega))
    (fun b6 ⟨m6, c6, t6⟩ n6 hn6 => ?_)
  refine Hs.then (hs_copy C gTG t3 b6 (by decide)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  have i7 : C.inp.drop (b6.set gTG (b6.env t3)).ip = natWord bits.length ++ ((bits ++ vs).flatMap natWord ++
      rest) := by
    rw [DS.set_ip, m6.ip, drop_step i5', List.flatMap_cons, List.append_assoc]
  refine Hs.then (copyNatS_spec 1 _ (cst_set c6 _ (by decide)) bits.length _ i7
    (by have := mem bits.length (by simp [ctxNats]); omega)) (fun b8 ⟨m8, c8, t8⟩ n8 hn8 => ?_)
  refine Hs.then (hs_copy C gN t3 b8 (by decide)) (fun b9 hb9 n9 hn9 => ?_)
  subst hb9
  have hsZ : ∀ m : Fin MM, b8.ram m = a.ram m ∧ b8.rc m = a.rc m := fun m => by
    refine ⟨?_, ?_⟩
    · rw [m8.ram, DS.set_ram, m6.ram, r5.ram m (by simp), m4.ram, DS.set_ram, m2.ram, r1.ram m (by simp)]
    · rw [m8.rc, DS.set_rc, m6.rc, r5.rc m (by simp), m4.rc, DS.set_rc, m2.rc, r1.rc m (by simp)]
  refine Hs.last (certS_spec _ (cst_set c8 _ (by decide)) bits vs rest (by rw [DS.set_ip, m8.ip]; exact drop_step i7)
    (by rw [DS.set_env_self, t8]) (by rw [DS.set_ram, (hsZ sZc).1, hZ]) (by rw [DS.set_rc, (hsZ sZc).2, hZc]) ℓ
    (fun v h => mem v (by simp [ctxNats, h])) hℓ hs) (fun b10 ⟨r10, e10, z10, zc10, c10, i10⟩ n10 hn10 => ?_)
  refine ⟨⟨?_, ?_, e10, z10, zc10, c10, i10⟩, ?_⟩
  · have hr := ((((((((((r1.weaken wC wS).trans (Ran.of_moved m2 [sZc] |>.weaken wC (fun _ h => h))).set
      (x := cN) _ (by decide)).trans ((Ran.of_moved m4 [sZc]).weaken (fun y hy => by revert y; decide)
        (fun _ h => h))).trans (r5.weaken wC wS)).trans ((Ran.of_moved m6 [sZc]).weaken wC (fun _ h => h))).set
      (x := gTG) _ (by decide)).trans ((Ran.of_moved m8 [sZc]).weaken wC (fun _ h => h))).set (x := gN) _
      (by decide)).trans (r10.weaken (fun y hy => by revert y; decide) (fun _ h => h)))
    refine hr.eqk ?_ ?_
    · simp only [ctxNats, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append,
        List.append_nil]
      omega
    · simp only [ctxNats, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, marksD_append,
        List.append_assoc]
  · rw [r10.fr gTG (by decide), DS.set_env_ne _ _ (show gTG ≠ gN by decide), m8.fr gTG (by decide),
      DS.set_env_self, t6]
  · unfold ctxCost
    have p1 := Nat.mul_le_mul_left fs.length (show copyCost 1 ℓ + 4 ≤ copyCost 1 ℓ + 9 by omega)
    have p2 : copyCost 1 (natBitLength fs.length) ≤ copyCost 1 ℓ := copyCost_mono (mem _ (by simp [ctxNats]))
    have p3 : copyCost 1 (natBitLength tg) ≤ copyCost 1 ℓ := copyCost_mono (mem _ (by simp [ctxNats]))
    have p4 : copyCost 1 (natBitLength bits.length) ≤ copyCost 1 ℓ := copyCost_mono (mem _ (by simp [ctxNats]))
    have e : (fs.length + bits.length + 20) * (copyCost 1 ℓ + 9) = fs.length * (copyCost 1 ℓ + 9) +
        bits.length * (copyCost 1 ℓ + 9) + 20 * copyCost 1 ℓ + 180 := by ring
    rw [e]
    omega

end NearQuarticWires.Reconstruct.GatherProg
