import Proof.Quartic.Reconstruct.EmitHead

/-!
# The context-reading program

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`headS` reads `n`, the scalars `M_1, A, Λ, J`, the rates, the bit of two circuits, `2mG_1`, `2mG_2`, `n_col`, the
number of tables per group, the certified bits and the number `m` of systems, and writes `frame (natWord n)` and
`natWord m` at depth `1` (`headS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)

variable {C : Ctx}

/-- The context: `n`. -/
def kN : Fin VV := ⟨81, by decide⟩
/-- The number of columns (read past). -/
def kC : Fin VV := ⟨82, by decide⟩
/-- The number of tables per group (read past). -/
def kG : Fin VV := ⟨83, by decide⟩
/-- The store of the certified bits (read past). -/
def sZ : Fin MM := ⟨4, by decide⟩

/-- Read the context and the number of systems; write `frame (natWord n)` and `natWord m` at depth `1`. -/
def headS : St VV MM :=
  .seq (rdVars [kN]) (.seq (.op (.copy t3 kN)) (.seq (emitNatD 2) (.seq (putD 1 false)
  (.seq (rdVars [kM, kA, kL, kJ]) (.seq (readListS sF) (.seq (rdVars [kPair, kB0, kB1, kC, kG])
  (.seq (readListS sZ) (.seq (rdVars [eM]) (.seq (.op (.copy t3 eM)) (emitNatD 1))))))))))

/-- The cost of `headS` with numbers of at most `ℓ` bits, `F` rates and `Z` certified bits. -/
def headCost (ℓ F Z : ℕ) : ℕ := (F + Z + 13) * (30 * ℓ + 36) + 2 * emitNatDCost 2 ℓ + 200

/-- The words read by `headS`. -/
def headWord (n M A L J pr B0 B1 nc tg m : ℕ) (fs bits : List ℕ) : List Bool :=
  natWord n ++ ([M, A, L, J].flatMap natWord ++ (listWord natWord fs ++
    ([pr, B0, B1, nc, tg].flatMap natWord ++ (listWord natWord bits ++ natWord m))))

theorem emitNatDCost_mono (d : ℕ) {x y : ℕ} (h : x ≤ y) : emitNatDCost d x ≤ emitNatDCost d y := by
  unfold emitNatDCost; exact Nat.mul_le_mul_left _ (by omega)

theorem emitNatDCost_depth (x : ℕ) : emitNatDCost 1 x ≤ emitNatDCost 2 x := by
  unfold emitNatDCost; exact Nat.mul_le_mul_right _ (by norm_num)

/-- **Reading the context.** -/
theorem headS_spec (a : DS VV MM) (hc : Cst a) (n M A L J pr B0 B1 nc tg m : ℕ) (fs bits : List ℕ)
    (rest : List Bool) (hin : C.inp.drop a.ip = headWord n M A L J pr B0 B1 nc tg m fs bits ++ rest)
    (hF : a.ram sF = [] ∧ a.rc sF = 0) (hZ : a.ram sZ = [] ∧ a.rc sZ = 0) (ℓ : ℕ)
    (hW : ∀ v ∈ [n, M, A, L, J, pr, B0, B1, nc, tg, m, fs.length, bits.length] ++ fs ++ bits, natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C headS a (headCost ℓ fs.length bits.length)
      (fun b => b.env kM = M ∧ b.env kA = A ∧ b.env kL = L ∧ b.env kJ = J ∧ b.env kPair = pr ∧ b.env kB0 = B0 ∧
        b.env kB1 = B1 ∧ b.env eM = m ∧ b.ram sF = fs ∧ b.rc sF = fs.length ∧
        b.ip = a.ip + (headWord n M A L J pr B0 B1 nc tg m fs bits).length ∧
        b.out = a.out ++ (marksD 2 (natWord n) ++ bitD 1 false ++ marksD 1 (natWord m)) ∧
        (∀ s, s ≠ sF → s ≠ sZ → b.ram s = a.ram s ∧ b.rc s = a.rc s) ∧ Cst b) := by
  have hv : ∀ v ∈ [n, M, A, L, J, pr, B0, B1, nc, tg, m, fs.length, bits.length] ++ fs ++ bits, natBitLength v ≤ ℓ :=
    hW
  have hWl : ℓ < 2 ^ C.Wd := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsFZ : sF ≠ sZ := by decide
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  -- n
  have hin1 : C.inp.drop a.ip = [n].flatMap natWord ++ ([M, A, L, J].flatMap natWord ++ (listWord natWord fs ++
      ([pr, B0, B1, nc, tg].flatMap natWord ++ (listWord natWord bits ++ (natWord m ++ rest))))) := by
    rw [hin]; unfold headWord; simp [List.append_assoc]
  refine Hx.hs (Hs.then (rdVars_spec [kN] (by decide) (by decide) [n] rfl a hc _ hin1 ℓ
    (fun v hv' => hv v (by simp at hv'; simp [hv'])) hℓ) (fun b1 ⟨e1, m1, c1⟩ k1 hk1 => ?_))
  have v1N : b1.env kN = n := e1 (kN, n) (by simp)
  refine Hs.then (hs_copy C t3 kN b1 (by decide)) (fun b2 hb2 k2 hk2 => ?_)
  subst hb2
  have c2 : Cst (b1.set t3 (b1.env kN)) := ⟨by vsimp [c1.z], by vsimp [c1.one], by vsimp [c1.two]⟩
  refine Hs.then (emitNatD_spec 2 _ c2 (by omega) (by
    rw [DS.set_env_self, v1N]; have := hv n (by simp); omega)) (fun b3 ⟨w3, c3⟩ k3 hk3 => ?_)
  refine Hs.then (putD_spec 1 false b3) (fun b4 w4 k4 hk4 => ?_)
  have c4 : Cst b4 := w4.cst c3 (by decide)
  -- M, A, L, J
  have hin4 : C.inp.drop b4.ip = [M, A, L, J].flatMap natWord ++ (listWord natWord fs ++
      ([pr, B0, B1, nc, tg].flatMap natWord ++ (listWord natWord bits ++ (natWord m ++ rest)))) := by
    rw [w4.ip, w3.ip, DS.set_ip, m1.ip]; exact drop_step hin1
  refine Hs.then (rdVars_spec [kM, kA, kL, kJ] (by decide) (by decide) [M, A, L, J] rfl b4 c4 _ hin4 ℓ
    (fun v hv' => hv v (by simp at hv'; simp only [List.mem_append, List.mem_cons]; tauto)) hℓ)
    (fun b5 ⟨e5, m5, c5⟩ k5 hk5 => ?_)
  -- the rates
  have hin5 : C.inp.drop b5.ip = listWord natWord fs ++
      ([pr, B0, B1, nc, tg].flatMap natWord ++ (listWord natWord bits ++ (natWord m ++ rest))) := by
    rw [m5.ip]; exact drop_step hin4
  have hF5 : b5.ram sF = [] ∧ b5.rc sF = 0 := by
    rw [m5.ram, m5.rc, w4.ram, w4.rc, w3.ram, w3.rc, DS.set_ram, DS.set_rc, m1.ram, m1.rc]; exact hF
  refine Hs.then (readListS_spec sF b5 c5 fs _ hin5 hF5.1 hF5.2 ℓ (fun v hv' => hv v (by
    rcases List.mem_cons.mp hv' with h | h
    · simp [h]
    · simp [h])) hℓ) (fun b6 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, c6⟩ k6 hk6 => ?_)
  -- pair, 2mG_1, 2mG_2, n_col, tables per group
  have hin6 : C.inp.drop b6.ip = [pr, B0, B1, nc, tg].flatMap natWord ++
      (listWord natWord bits ++ (natWord m ++ rest)) := by
    rw [f3]; exact drop_step hin5
  refine Hs.then (rdVars_spec [kPair, kB0, kB1, kC, kG] (by decide) (by decide) [pr, B0, B1, nc, tg] rfl b6 c6 _
    hin6 ℓ (fun v hv' => hv v (by simp at hv'; simp only [List.mem_append, List.mem_cons]; tauto)) hℓ)
    (fun b7 ⟨e7, m7, c7⟩ k7 hk7 => ?_)
  -- the certified bits
  have hin7 : C.inp.drop b7.ip = listWord natWord bits ++ (natWord m ++ rest) := by
    rw [m7.ip]; exact drop_step hin6
  have hZ7 : b7.ram sZ = [] ∧ b7.rc sZ = 0 := by
    rw [m7.ram, m7.rc, (f5 sZ hsFZ.symm).1, (f5 sZ hsFZ.symm).2, m5.ram, m5.rc, w4.ram, w4.rc, w3.ram, w3.rc,
      DS.set_ram, DS.set_rc, m1.ram, m1.rc]; exact hZ
  refine Hs.then (readListS_spec sZ b7 c7 bits _ hin7 hZ7.1 hZ7.2 ℓ (fun v hv' => hv v (by
    rcases List.mem_cons.mp hv' with h | h
    · simp [h]
    · simp [h])) hℓ) (fun b8 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, c8⟩ k8 hk8 => ?_)
  -- the number of systems
  have hin8 : C.inp.drop b8.ip = [m].flatMap natWord ++ rest := by
    rw [g3]; simpa using drop_step hin7
  refine Hs.then (rdVars_spec [eM] (by decide) (by decide) [m] rfl b8 c8 _ hin8 ℓ
    (fun v hv' => hv v (by simp at hv'; simp [hv'])) hℓ) (fun b9 ⟨e9, m9, c9⟩ k9 hk9 => ?_)
  have v9M : b9.env eM = m := e9 (eM, m) (by simp)
  refine Hs.then (hs_copy C t3 eM b9 (by decide)) (fun b10 hb10 k10 hk10 => ?_)
  subst hb10
  have c10 : Cst (b9.set t3 (b9.env eM)) := ⟨by vsimp [c9.z], by vsimp [c9.one], by vsimp [c9.two]⟩
  refine Hs.last (emitNatD_spec 1 _ c10 (by omega) (by
    rw [DS.set_env_self, v9M]; have := hv m (by simp); omega)) (fun b11 ⟨w11, c11⟩ k11 hk11 => ?_)
  -- the values kept to the end
  have fr11 : ∀ y, y ∉ t3 :: emitNatDT → b11.env y = b9.env y := fun y hy => by
    rw [w11.fr y (fun h => hy (List.mem_cons_of_mem _ h)),
      DS.set_env_ne _ _ (fun h => hy (by rw [h]; exact List.mem_cons_self))]
  have fr9 : ∀ y, y ∉ [eM, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vJ, lN, lK] → b11.env y = b7.env y := by
    intro y hy
    rw [fr11 y (fun h => hy (by revert h; revert y; decide)), m9.fr y (fun h => hy (by revert h; revert y; decide)),
      g9 y (fun h => hy (by revert h; revert y; decide))]
  have fr7 : ∀ y, y ∉ [kPair, kB0, kB1, kC, kG, eM, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vJ, lN, lK] →
      b11.env y = b5.env y := by
    intro y hy
    rw [fr9 y (fun h => hy (by revert h; revert y; decide)), m7.fr y (fun h => hy (by revert h; revert y; decide)),
      f9 y (fun h => hy (by revert h; revert y; decide))]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, c11⟩, ?_⟩
  · rw [fr7 kM (by decide)]; exact e5 (kM, M) (by simp)
  · rw [fr7 kA (by decide)]; exact e5 (kA, A) (by simp)
  · rw [fr7 kL (by decide)]; exact e5 (kL, L) (by simp)
  · rw [fr7 kJ (by decide)]; exact e5 (kJ, J) (by simp)
  · rw [fr9 kPair (by decide)]; exact e7 (kPair, pr) (by simp)
  · rw [fr9 kB0 (by decide)]; exact e7 (kB0, B0) (by simp)
  · rw [fr9 kB1 (by decide)]; exact e7 (kB1, B1) (by simp)
  · rw [fr11 eM (by decide), v9M]
  · rw [w11.ram, DS.set_ram, m9.ram, (g5 sF hsFZ).1, m7.ram, f1]
  · rw [w11.rc, DS.set_rc, m9.rc, (g5 sF hsFZ).2, m7.rc, f2]
  · rw [w11.ip, DS.set_ip, m9.ip, g3, m7.ip, f3, m5.ip, w4.ip, w3.ip, DS.set_ip, m1.ip]
    unfold headWord
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega
  · rw [w11.out, DS.set_out, m9.out, g4, m7.out, f4, m5.out, w4.out, w3.out, DS.set_out, m1.out]
    simp only [List.append_nil, List.append_assoc, DS.set_env_self, v9M, v1N]
  · intro s h1 h2
    rw [w11.ram, w11.rc, DS.set_ram, DS.set_rc, m9.ram, m9.rc, (g5 s h2).1, (g5 s h2).2, m7.ram, m7.rc,
      (f5 s h1).1, (f5 s h1).2, m5.ram, m5.rc, w4.ram, w4.rc, w3.ram, w3.rc, DS.set_ram, DS.set_rc, m1.ram, m1.rc]
    exact ⟨rfl, rfl⟩
  · -- the cost
    have hn := hv n (by simp)
    have hm := hv m (by simp)
    rw [DS.set_env_self, v1N] at hk3
    rw [DS.set_env_self, v9M] at hk11
    have h3 := emitNatDCost_mono 2 hn
    have h11 := (emitNatDCost_mono 1 hm).trans (emitNatDCost_depth ℓ)
    have hp : 2 * 2 ^ 1 + 1 = 5 := by norm_num
    rw [hp] at hk4
    simp only [List.length_cons, List.length_nil] at hk1 hk5 hk7 hk9
    have hr : (fs.length + bits.length + 13) * (30 * ℓ + 36) =
        fs.length * (30 * ℓ + 36) + bits.length * (30 * ℓ + 36) + 13 * (30 * ℓ + 36) := by ring
    unfold headCost
    omega

end NearQuarticWires.Reconstruct
