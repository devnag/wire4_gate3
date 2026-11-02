import Proof.Quartic.Reconstruct.GatherProgRecs

/-!
# The gathering program: writing the gathered items of a group

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

After the sort, position `t = j·tg + k` of the store `sR` holds `t·PW + c` with `c` the count of the `j`-th
certified column in table `k` (`GatherProgRecs.recsK_sort`). `gItemsS` writes, for every certified column `j`, the
gathered item: the part, the digits (from `sHd`), the number `tg` of rows and the rows `(p, 2, |ρ_1|, |ρ_2|, c)`
(from `sI` and `sR`), all at depth `1` (`gItemsS_spec`).
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

/-! ## The programs -/

/-- The digits from the store `sHd` (two numbers per digit). -/
def gEmitDS : St VV MM := .seq (.op (.rwM sHd)) (.seq (.op (.zero gK)) (.loop (.lt gK gDn)
  (.seq (.op (.rdM sHd t3)) (.seq (emitNatD 1) (.seq (.op (.rdM sHd t3)) (.seq (emitNatD 1) (.op (.inc gK))))))))

/-- Read the record at the cursor of store `m` and write it. -/
def rdEmS (m : Fin MM) : St VV MM := .seq (.op (.rdM m t3)) (emitNatD 1)

/-- Write the number held in `x`. -/
def cpEmS (x : Fin VV) : St VV MM := .seq (.op (.copy t3 x)) (emitNatD 1)

/-- Read a record of `sR` and write its count (the record modulo `PW`). -/
def cntEmS : St VV MM := .seq (.op (.rdM sR gRec)) (.seq (.op (.dm gRec gPW gQ t3)) (emitNatD 1))

/-- One row `(p, 2, |ρ_1|, |ρ_2|, c)` of an item. -/
def gRowS : St VV MM := .seq (rdEmS sI) (.seq (cpEmS v2) (.seq (rdEmS sI) (.seq (rdEmS sI) (.seq cntEmS
  (.op (.inc gTk))))))

/-- The rows of an item. -/
def gRowsS : St VV MM := .seq (.op (.rwM sI)) (.seq (.op (.zero gTk)) (.loop (.lt gTk gTG) gRowS))

/-- One gathered item. -/
def gItemS : St VV MM := .seq (cpEmS gS) (.seq (cpEmS gDn) (.seq gEmitDS (.seq (cpEmS gTG) (.seq gRowsS
  (.op (.inc gJ))))))

/-- The gathered items of a group. -/
def gItemsS : St VV MM := .seq (.op (.zero gJ)) (.loop (.lt gJ gCC) gItemS)

/-- The variables written by the emission. -/
def emT : List (Fin VV) := [gK, gTk, gRec, gQ, t3, t5, t6, t7, t8, t9, vJ]

/-- The variables written by the writing of one number. -/
def emT0 : List (Fin VV) := [gRec, gQ, t3, t5, t6, t7, t8, t9, vJ]

/-! ## Lists read by position -/

/-- The first `n` records of a store. -/
def pre (L : List ℕ) (n : ℕ) : List ℕ := (List.range n).map fun i => L.getD i 0

theorem pre_succ (L : List ℕ) (n : ℕ) : pre L (n + 1) = pre L n ++ [L.getD n 0] := by
  simp [pre, List.range_succ]

theorem pre_length (L : List ℕ) : pre L L.length = L := by
  apply List.ext_getElem (by simp [pre])
  intro i h1 h2
  simp [pre, List.getElem?_eq_getElem h2]

theorem emT_cst : vZ ∉ emT ∧ v1 ∉ emT ∧ v2 ∉ emT := by decide

/-! ## The digits -/

theorem gEmitDS_spec (a : DS VV MM) (hc : Cst a) (DN : List ℕ) (D : ℕ) (hDN : DN.length = 2 * D)
    (hH : a.ram sHd = DN) (hD : a.env gDn = D) (ℓ : ℕ) (hv : ∀ v ∈ DN, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hDW : D < 2 ^ C.Wd) :
    Hs C gEmitDS a (a.rc sHd + D * (2 * unitC ℓ + 9) + 6)
      (fun b => Ran a b 0 (marksD 1 (DN.flatMap natWord)) emT [sHd] ∧ b.rc sHd = DN.length ∧ b.ram sHd = DN ∧
        Cst b) := by
  have hvg : ∀ i, i < DN.length → natBitLength (DN.getD i 0) ≤ ℓ := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]; exact hv _ (List.getElem_mem _)
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gK = k ∧ b.env gDn = D ∧ b.ram sHd = DN ∧ b.rc sHd = 2 * k ∧
    Ran a b 0 (marksD 1 ((pre DN (2 * k)).flatMap natWord)) emT [sHd] ∧ Cst b
  have loop := loopCnt (C := C) gK gDn (by decide) (.seq (.op (.rdM sHd t3)) (.seq (emitNatD 1) (.seq
    (.op (.rdM sHd t3)) (.seq (emitNatD 1) (.op (.inc gK)))))) D (2 * unitC ℓ + 7) I
    (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6⟩
      refine (Hs.seq (t1 := 1) (t2 := 2 * unitC ℓ + 5) (hs_rdM C sHd t3 b (by rw [h3, h4, hDN]; omega))
        (fun d1 hd1 => ?_)).mono (by omega) (fun _ h => h)
      have d1t : d1.env t3 = DN.getD (2 * k) 0 := by rw [hd1, DS.adv_env, DS.set_env_self, h3, h4]
      have r1 : Ran b d1 0 [] [t3] [sHd] := by
        rw [hd1]; exact ((Ran.refl b [t3] [sHd]).set _ (by decide)).adv (m := sHd) (by simp)
      have c1 : Cst d1 := r1.cst h6 (by decide)
      refine (Hs.seq (t1 := unitC ℓ) (t2 := unitC ℓ + 4) (emN_spec d1 c1 ℓ (by rw [d1t]; exact hvg _ (by omega)) hℓ)
        (fun d2 ⟨r2, c2⟩ => ?_)).mono (by omega) (fun _ h => h)
      have d2r : d2.ram sHd = DN ∧ d2.rc sHd = 2 * k + 1 := by
        rw [r2.ram sHd (by simp), r2.rc sHd (by simp), hd1]
        simp only [DS.adv_ram, DS.set_ram, DS.adv_rc_self, DS.set_rc, h3, h4]; exact ⟨trivial, trivial⟩
      refine (Hs.seq (t1 := 1) (t2 := unitC ℓ + 2) (hs_rdM C sHd t3 d2 (by rw [d2r.1, d2r.2, hDN]; omega))
        (fun d3 hd3 => ?_)).mono (by omega) (fun _ h => h)
      have d3t : d3.env t3 = DN.getD (2 * k + 1) 0 := by rw [hd3, DS.adv_env, DS.set_env_self, d2r.1, d2r.2]
      have r3 : Ran d2 d3 0 [] [t3] [sHd] := by
        rw [hd3]; exact ((Ran.refl d2 [t3] [sHd]).set _ (by decide)).adv (m := sHd) (by simp)
      have c3 : Cst d3 := r3.cst c2 (by decide)
      refine (Hs.seq (t1 := unitC ℓ) (t2 := 1) (emN_spec d3 c3 ℓ (by rw [d3t]; exact hvg _ (by omega)) hℓ)
        (fun d4 ⟨r4, c4⟩ => ?_)).mono (by omega) (fun _ h => h)
      have d4K : d4.env gK = k := by
        rw [r4.fr gK (by decide), r3.fr gK (by decide), r2.fr gK (by decide), r1.fr gK (by decide), h1]
      refine Hs.mono (hs_inc C gK d4 (by rw [d4K]; omega)) le_rfl ?_
      rintro d5 rfl
      refine ⟨by rw [DS.set_env_self, d4K], ?_, ?_, ?_, ?_, cst_set c4 _ (by decide)⟩
      · rw [DS.set_env_ne _ _ (show gDn ≠ gK by decide), r4.fr gDn (by decide), r3.fr gDn (by decide),
          r2.fr gDn (by decide), r1.fr gDn (by decide), h2]
      · rw [DS.set_ram, r4.ram sHd (by simp), hd3]; simp only [DS.adv_ram, DS.set_ram, d2r.1]
      · rw [DS.set_rc, r4.rc sHd (by simp), hd3]; simp only [DS.adv_rc_self, DS.set_rc, d2r.2]; omega
      · have w1 : ∀ y ∈ [t3], y ∈ emT := fun y hy => by revert y; decide
        have w2 : ∀ y ∈ emitNatDT, y ∈ emT := fun y hy => by revert y; decide
        have hr := (((h5.trans (r1.weaken w1 (fun _ h => h))).trans (r2.weaken w2 (fun _ h => by simp at h))).trans
          (r3.weaken w1 (fun _ h => h))).trans (r4.weaken w2 (fun _ h => by simp at h)) |>.set (x := gK)
          (d4.env gK + 1) (by decide)
        refine hr.eqk (by simp) ?_
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pre_succ, pre_succ, d1t, d3t]
        simp only [List.flatMap_append, List.flatMap_singleton, marksD_append, List.append_nil, List.append_assoc])
  refine Hx.hs (Hs.then (hs_rwM C sHd a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C gK _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hD], by simp only [DS.set_ram, DS.rew_ram, hH],
    by rw [DS.set_rc, DS.rew_rc_self], ?_, cst_set (cst_rew hc _) _ (by decide)⟩)
    (fun b ⟨_, _, h3, h4, h5, h6⟩ n hn => ⟨⟨?_, by rw [h4, hDN], h3, h6⟩, ?_⟩)
  · exact (((Ran.refl a emT [sHd]).rew (m := sHd) (by simp)).set (x := gK) 0 (by decide)).eqk rfl
      (by simp [pre, marksD])
  · rw [← hDN, pre_length] at h5; exact h5
  · have e : D * (2 * unitC ℓ + 7 + 2) = D * (2 * unitC ℓ + 9) := by ring
    omega

/-! ## Writing one number -/

theorem rdEmS_spec (m : Fin MM) (a : DS VV MM) (hc : Cst a) (L : List ℕ) (hL : a.ram m = L)
    (hr : a.rc m < L.length) (ℓ : ℕ) (hv : natBitLength (L.getD (a.rc m) 0) ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (rdEmS m) a (unitC ℓ + 2) (fun b => Ran a b 0 (marksD 1 (natWord (L.getD (a.rc m) 0))) emT0 [m] ∧
      b.ram m = L ∧ b.rc m = a.rc m + 1 ∧ Cst b) := by
  refine (Hs.seq (t1 := 1) (t2 := unitC ℓ) (hs_rdM C m t3 a (by rw [hL]; exact hr)) (fun d1 hd1 => ?_)).mono
    (by omega) (fun _ h => h)
  have d1t : d1.env t3 = L.getD (a.rc m) 0 := by rw [hd1, DS.adv_env, DS.set_env_self, hL]
  have r1 : Ran a d1 0 [] [t3] [m] := by
    rw [hd1]; exact ((Ran.refl a [t3] [m]).set _ (by simp)).adv (m := m) (by simp)
  have c1 : Cst d1 := r1.cst hc (by decide)
  refine (emN_spec d1 c1 ℓ (by rw [d1t]; exact hv) hℓ).mono le_rfl ?_
  rintro d2 ⟨r2, c2⟩
  refine ⟨?_, ?_, ?_, c2⟩
  · exact ((r1.weaken (fun y hy => by revert y; decide) (fun _ h => h)).trans
      (r2.weaken (fun y hy => by revert y; decide) (fun _ h => by simp at h))).eqk (by simp) (by rw [d1t]; simp)
  · rw [r2.ram m (by simp), hd1]; simp [hL]
  · rw [r2.rc m (by simp), hd1]; simp

theorem cpEmS_spec (x : Fin VV) (hx : x ≠ t3) (a : DS VV MM) (hc : Cst a) (ℓ : ℕ)
    (hv : natBitLength (a.env x) ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (cpEmS x) a (unitC ℓ + 2) (fun b => Ran a b 0 (marksD 1 (natWord (a.env x))) emT0 [] ∧ Cst b) := by
  refine (Hs.seq (t1 := 1) (t2 := unitC ℓ) (hs_copy C t3 x a (Ne.symm hx)) (fun d1 hd1 => ?_)).mono
    (by omega) (fun _ h => h)
  have d1t : d1.env t3 = a.env x := by rw [hd1, DS.set_env_self]
  have r1 : Ran a d1 0 [] [t3] [] := by rw [hd1]; exact (Ran.refl a [t3] []).set _ (by simp)
  have c1 : Cst d1 := r1.cst hc (by decide)
  refine (emN_spec d1 c1 ℓ (by rw [d1t]; exact hv) hℓ).mono le_rfl ?_
  rintro d2 ⟨r2, c2⟩
  exact ⟨((r1.weaken (fun y hy => by revert y; decide) (fun _ h => h)).trans
      (r2.weaken (fun y hy => by revert y; decide) (fun _ h => h))).eqk (by simp) (by rw [d1t]; simp), c2⟩

theorem cntEmS_spec (a : DS VV MM) (hc : Cst a) (RL : List ℕ) (hR : a.ram sR = RL) (hr : a.rc sR < RL.length)
    (PW : ℕ) (hPW : a.env gPW = PW) (hP0 : 0 < PW) (hP2 : 2 * PW ≤ 2 ^ C.Wd) (ℓ : ℕ)
    (hv : natBitLength (RL.getD (a.rc sR) 0 % PW) ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C cntEmS a (unitC ℓ + 4) (fun b => Ran a b 0 (marksD 1 (natWord (RL.getD (a.rc sR) 0 % PW))) emT0 [sR] ∧
      b.ram sR = RL ∧ b.rc sR = a.rc sR + 1 ∧ Cst b) := by
  refine (Hs.seq (t1 := 1) (t2 := unitC ℓ + 2) (hs_rdM C sR gRec a (by rw [hR]; exact hr)) (fun d1 hd1 => ?_)).mono
    (by omega) (fun _ h => h)
  have d1R : d1.env gRec = RL.getD (a.rc sR) 0 := by rw [hd1, DS.adv_env, DS.set_env_self, hR]
  have d1P : d1.env gPW = PW := by rw [hd1, DS.adv_env, DS.set_env_ne _ _ (show gPW ≠ gRec by decide), hPW]
  have r1 : Ran a d1 0 [] [gRec] [sR] := by
    rw [hd1]; exact ((Ran.refl a [gRec] [sR]).set _ (by simp)).adv (m := sR) (by simp)
  refine (Hs.seq (t1 := 1) (t2 := unitC ℓ) (hs_dm C gRec gPW gQ t3 d1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [d1P]; exact hP0) (by rw [d1P]; exact hP2)) (fun d2 hd2 => ?_)).mono
    (by omega) (fun _ h => h)
  have d2t : d2.env t3 = RL.getD (a.rc sR) 0 % PW := by rw [hd2, DS.set_env_self, d1R, d1P]
  have r2 : Ran d1 d2 0 [] [gQ, t3] [] := by
    rw [hd2]; exact ((Ran.refl d1 [gQ, t3] []).set _ (by simp)).set _ (by simp)
  have c2 : Cst d2 := r2.cst (r1.cst hc (by decide)) (by decide)
  refine (emN_spec d2 c2 ℓ (by rw [d2t]; exact hv) hℓ).mono le_rfl ?_
  rintro d3 ⟨r3, c3⟩
  refine ⟨?_, ?_, ?_, c3⟩
  · exact (((r1.weaken (fun y hy => by revert y; decide) (fun _ h => h)).trans
      (r2.weaken (fun y hy => by revert y; decide) (fun _ h => by simp at h))).trans
      (r3.weaken (fun y hy => by revert y; decide) (fun _ h => by simp at h))).eqk (by simp) (by rw [d2t]; simp)
  · rw [r3.ram sR (by simp), r2.ram sR (by simp), hd1]; simp [hR]
  · rw [r3.rc sR (by simp), r2.rc sR (by simp), hd1]; simp

/-! ## The rows of an item -/

/-- The numbers of row `k` of an item whose records start at position `r` of the store `sR`. -/
def rowN (IL RL : List ℕ) (PW r k : ℕ) : List ℕ :=
  [IL.getD (3 * k) 0, 2, IL.getD (3 * k + 1) 0, IL.getD (3 * k + 2) 0, RL.getD (r + k) 0 % PW]

theorem gRowS_spec (a : DS VV MM) (hc : Cst a) (IL RL : List ℕ) (PW r k : ℕ) (hI : a.ram sI = IL)
    (hIc : a.rc sI = 3 * k) (hIl : 3 * k + 2 < IL.length) (hR : a.ram sR = RL) (hRc : a.rc sR = r + k)
    (hRl : r + k < RL.length) (hK : a.env gTk = k) (hPW : a.env gPW = PW) (hP0 : 0 < PW)
    (hP2 : 2 * PW ≤ 2 ^ C.Wd) (ℓ : ℕ) (hv : ∀ v ∈ rowN IL RL PW r k, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hKW : k + 1 < 2 ^ C.Wd) :
    Hs C gRowS a (5 * unitC ℓ + 20) (fun b => Ran a b 0 (marksD 1 ((rowN IL RL PW r k).flatMap natWord)) emT
      [sI, sR] ∧ b.ram sI = IL ∧ b.rc sI = 3 * k + 3 ∧ b.ram sR = RL ∧ b.rc sR = r + k + 1 ∧ b.env gTk = k + 1 ∧
      Cst b) := by
  have v := fun i (h : i < 5) => hv _ (List.getElem_mem (l := rowN IL RL PW r k) (n := i) (by simp [rowN]; omega))
  have wI : ∀ m ∈ [sI], m ∈ [sI, sR] := fun m h => by simp at h; simp [h]
  have wR : ∀ m ∈ [sR], m ∈ [sI, sR] := fun m h => by simp at h; simp [h]
  have w0 : ∀ m ∈ ([] : List (Fin MM)), m ∈ [sI, sR] := fun m h => by simp at h
  have wT : ∀ y ∈ emT0, y ∈ emT := fun y hy => by revert y; decide
  refine Hx.hs (Hs.then (rdEmS_spec sI a hc IL hI (by omega) ℓ (by rw [hIc]; exact v 0 (by norm_num)) hℓ)
    (fun b1 ⟨r1, i1, c1, k1⟩ n1 hn1 => ?_))
  refine Hs.then (cpEmS_spec v2 (by decide) b1 k1 ℓ (by rw [k1.two]; exact v 1 (by norm_num)) hℓ)
    (fun b2 ⟨r2, k2⟩ n2 hn2 => ?_)
  have b2I : b2.ram sI = IL ∧ b2.rc sI = 3 * k + 1 := ⟨by rw [r2.ram sI (by simp), i1],
    by rw [r2.rc sI (by simp), c1, hIc]⟩
  refine Hs.then (rdEmS_spec sI b2 k2 IL b2I.1 (by omega) ℓ (by rw [b2I.2]; exact v 2 (by norm_num)) hℓ)
    (fun b3 ⟨r3, i3, c3, k3⟩ n3 hn3 => ?_)
  refine Hs.then (rdEmS_spec sI b3 k3 IL i3 (by omega) ℓ (by rw [c3, b2I.2]; exact v 3 (by norm_num)) hℓ)
    (fun b4 ⟨r4, i4, c4, k4⟩ n4 hn4 => ?_)
  have b4R : b4.ram sR = RL ∧ b4.rc sR = r + k := ⟨by
      rw [r4.ram sR (by decide), r3.ram sR (by decide), r2.ram sR (by simp), r1.ram sR (by decide), hR],
    by rw [r4.rc sR (by decide), r3.rc sR (by decide), r2.rc sR (by simp), r1.rc sR (by decide), hRc]⟩
  have b4P : b4.env gPW = PW := by
    rw [r4.fr gPW (by decide), r3.fr gPW (by decide), r2.fr gPW (by decide), r1.fr gPW (by decide), hPW]
  refine Hs.then (cntEmS_spec b4 k4 RL b4R.1 (by rw [b4R.2]; exact hRl) PW b4P hP0 hP2 ℓ
    (by rw [b4R.2]; exact v 4 (by norm_num)) hℓ) (fun b5 ⟨r5, i5, c5, k5⟩ n5 hn5 => ?_)
  have b5K : b5.env gTk = k := by
    rw [r5.fr gTk (by decide), r4.fr gTk (by decide), r3.fr gTk (by decide), r2.fr gTk (by decide),
      r1.fr gTk (by decide), hK]
  refine Hs.last (hs_inc C gTk b5 (by rw [b5K]; exact hKW)) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, by rw [DS.set_env_self, b5K], cst_set k5 _ (by decide)⟩, ?_⟩
  · have hr := ((((r1.weaken wT wI).trans (r2.weaken wT w0)).trans (r3.weaken wT wI)).trans (r4.weaken wT wI)).trans
      (r5.weaken wT wR) |>.set (x := gTk) (b5.env gTk + 1) (by decide)
    refine hr.eqk (by simp) ?_
    rw [hIc] at *
    simp only [rowN, List.flatMap_cons, List.flatMap_nil, List.append_nil, marksD_append, List.append_assoc,
      List.nil_append, c3, b2I.2, b4R.2, k1.two]
  · rw [DS.set_ram, r5.ram sI (by decide), i4]
  · rw [DS.set_rc, r5.rc sI (by decide), c4, c3, b2I.2]
  · rw [DS.set_ram, i5]
  · rw [DS.set_rc, c5, b4R.2]
  · omega

/-- The rows of an item whose records start at position `r` of the store `sR`. -/
def rowsN (IL RL : List ℕ) (PW r tg : ℕ) : List ℕ := (List.range tg).flatMap (rowN IL RL PW r)

theorem gRowsS_spec (a : DS VV MM) (hc : Cst a) (IL RL : List ℕ) (PW r tg : ℕ) (hI : a.ram sI = IL)
    (hIl : 3 * tg ≤ IL.length) (hR : a.ram sR = RL) (hRc : a.rc sR = r) (hRl : r + tg ≤ RL.length)
    (hTG : a.env gTG = tg) (hPW : a.env gPW = PW) (hP0 : 0 < PW) (hP2 : 2 * PW ≤ 2 ^ C.Wd) (ℓ : ℕ)
    (hv : ∀ k < tg, ∀ v ∈ rowN IL RL PW r k, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (htg : tg < 2 ^ C.Wd) :
    Hs C gRowsS a (a.rc sI + tg * (5 * unitC ℓ + 22) + 6)
      (fun b => Ran a b 0 (marksD 1 ((rowsN IL RL PW r tg).flatMap natWord)) emT [sI, sR] ∧ b.ram sI = IL ∧
        b.rc sI = 3 * tg ∧ b.ram sR = RL ∧ b.rc sR = r + tg ∧ Cst b) := by
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gTk = k ∧ b.env gTG = tg ∧ b.env gPW = PW ∧ b.ram sI = IL ∧
    b.rc sI = 3 * k ∧ b.ram sR = RL ∧ b.rc sR = r + k ∧
    Ran a b 0 (marksD 1 ((rowsN IL RL PW r k).flatMap natWord)) emT [sI, sR] ∧ Cst b
  have loop := loopCnt (C := C) gTk gTG (by decide) gRowS tg (5 * unitC ℓ + 20) I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
    intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine (gRowS_spec b h9 IL RL PW r k h4 h5 (by omega) h6 h7 (by omega) h1 h3 hP0 hP2 ℓ (hv k hk) hℓ
      (by omega)).mono le_rfl ?_
    rintro d ⟨r1, e1, e2, e3, e4, e5, c1⟩
    refine ⟨e5, by rw [r1.fr gTG (by decide), h2], by rw [r1.fr gPW (by decide), h3], e1, by rw [e2]; ring, e3,
      by rw [e4]; ring, ?_, c1⟩
    refine (h8.trans r1).eqk rfl ?_
    simp only [rowsN, List.range_succ, List.flatMap_append, List.flatMap_singleton, marksD_append])
  refine Hx.hs (Hs.then (hs_rwM C sI a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C gTk _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hTG], by vsimp [hPW], by simp only [DS.set_ram, DS.rew_ram, hI],
    by rw [DS.set_rc, DS.rew_rc_self], by simp only [DS.set_ram, DS.rew_ram, hR],
    by rw [DS.set_rc, DS.rew_rc_ne _ (show sR ≠ sI by decide), hRc, Nat.add_zero],
    (((Ran.refl a emT [sI, sR]).rew (m := sI) (by simp)).set (x := gTk) 0 (by decide)).eqk rfl
      (by simp [rowsN, marksD]), cst_set (cst_rew hc _) _ (by decide)⟩)
    (fun b ⟨_, _, _, h4, h5, h6, h7, h8, h9⟩ n hn => ⟨⟨h8, h4, h5, h6, h7, h9⟩, ?_⟩)
  have e : tg * (5 * unitC ℓ + 20 + 2) = tg * (5 * unitC ℓ + 22) := by ring
  omega

/-! ## One item -/

/-- The numbers of the `j`-th gathered item of a group. -/
def itemN (s D : ℕ) (DN IL RL : List ℕ) (PW tg j : ℕ) : List ℕ :=
  [s, D] ++ DN ++ [tg] ++ rowsN IL RL PW (j * tg) tg

/-- The cost of one item. -/
def itemCostG (ℓ D tg : ℕ) : ℕ := 2 * D + 3 * tg + D * (2 * unitC ℓ + 9) + tg * (5 * unitC ℓ + 22) + 3 * unitC ℓ + 30

theorem gItemS_spec (a : DS VV MM) (hc : Cst a) (s D : ℕ) (DN IL RL : List ℕ) (PW tg j : ℕ) (hS : a.env gS = s)
    (hD : a.env gDn = D) (hDN : DN.length = 2 * D) (hH : a.ram sHd = DN) (hHc : a.rc sHd ≤ 2 * D)
    (hTG : a.env gTG = tg) (hI : a.ram sI = IL) (hIc : a.rc sI ≤ 3 * tg) (hIl : 3 * tg ≤ IL.length)
    (hR : a.ram sR = RL) (hRc : a.rc sR = j * tg) (hRl : j * tg + tg ≤ RL.length) (hJ : a.env gJ = j)
    (hPW : a.env gPW = PW) (hP0 : 0 < PW) (hP2 : 2 * PW ≤ 2 ^ C.Wd) (ℓ : ℕ)
    (hv : ∀ v ∈ itemN s D DN IL RL PW tg j, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hDW : D < 2 ^ C.Wd)
    (htg : tg < 2 ^ C.Wd) (hJW : j + 1 < 2 ^ C.Wd) :
    Hs C gItemS a (itemCostG ℓ D tg)
      (fun b => Ran a b 0 (marksD 1 ((itemN s D DN IL RL PW tg j).flatMap natWord)) (gJ :: emT) [sHd, sI, sR] ∧
        b.ram sHd = DN ∧ b.rc sHd = 2 * D ∧ b.ram sI = IL ∧ b.rc sI = 3 * tg ∧ b.ram sR = RL ∧
        b.rc sR = j * tg + tg ∧ b.env gJ = j + 1 ∧ Cst b) := by
  have vS : natBitLength s ≤ ℓ := hv s (by simp [itemN])
  have vD : natBitLength D ≤ ℓ := hv D (by simp [itemN])
  have vDN : ∀ x ∈ DN, natBitLength x ≤ ℓ := fun x h => hv x (by simp [itemN, h])
  have vT : natBitLength tg ≤ ℓ := hv tg (by simp [itemN])
  have vR : ∀ k < tg, ∀ x ∈ rowN IL RL PW (j * tg) k, natBitLength x ≤ ℓ := fun k hk x h =>
    hv x (by
      simp only [itemN, rowsN, List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inr ⟨k, hk, h⟩)
  have wE0 : ∀ y ∈ emT0, y ∈ gJ :: emT := fun y hy => by revert y; decide
  have wE : ∀ y ∈ emT, y ∈ gJ :: emT := fun y hy => List.mem_cons_of_mem _ hy
  refine Hx.hs (Hs.then (cpEmS_spec gS (by decide) a hc ℓ (by rw [hS]; exact vS) hℓ)
    (fun b1 ⟨r1, c1⟩ n1 hn1 => ?_))
  refine Hs.then (cpEmS_spec gDn (by decide) b1 c1 ℓ (by rw [r1.fr gDn (by decide), hD]; exact vD) hℓ)
    (fun b2 ⟨r2, c2⟩ n2 hn2 => ?_)
  have b2f : ∀ y, y ∉ emT0 → b2.env y = a.env y := fun y hy => by rw [r2.fr y hy, r1.fr y hy]
  have b2s : ∀ m : Fin MM, b2.ram m = a.ram m ∧ b2.rc m = a.rc m := fun m =>
    ⟨by rw [r2.ram m (by simp), r1.ram m (by simp)], by rw [r2.rc m (by simp), r1.rc m (by simp)]⟩
  refine Hs.then (gEmitDS_spec b2 c2 DN D hDN (by rw [(b2s sHd).1, hH]) (by rw [b2f gDn (by decide), hD]) ℓ vDN hℓ
    hDW) (fun b3 ⟨r3, c3, i3, k3⟩ n3 hn3 => ?_)
  refine Hs.then (cpEmS_spec gTG (by decide) b3 k3 ℓ (by rw [r3.fr gTG (by decide), b2f gTG (by decide), hTG]; exact vT)
    hℓ) (fun b4 ⟨r4, k4⟩ n4 hn4 => ?_)
  have b4f : ∀ y, y ∉ gJ :: emT → b4.env y = a.env y := fun y hy => by
    rw [r4.fr y (fun h => hy (wE0 y h)), r3.fr y (fun h => hy (wE y h)), b2f y (fun h => hy (wE0 y h))]
  have b4s : ∀ m : Fin MM, m ≠ sHd → b4.ram m = a.ram m ∧ b4.rc m = a.rc m := fun m hm =>
    ⟨by rw [r4.ram m (by simp), r3.ram m (by simpa using hm), (b2s m).1],
      by rw [r4.rc m (by simp), r3.rc m (by simpa using hm), (b2s m).2]⟩
  refine Hs.then (gRowsS_spec b4 k4 IL RL PW (j * tg) tg (by rw [(b4s sI (by decide)).1, hI]) hIl
    (by rw [(b4s sR (by decide)).1, hR]) (by rw [(b4s sR (by decide)).2, hRc]) hRl
    (by rw [b4f gTG (by decide), hTG]) (by rw [b4f gPW (by decide), hPW]) hP0 hP2 ℓ vR hℓ htg)
    (fun b5 ⟨r5, i5, c5, e5, f5, k5⟩ n5 hn5 => ?_)
  have b5J : b5.env gJ = j := by
    rw [r5.fr gJ (by decide), r4.fr gJ (by decide), r3.fr gJ (by decide), r2.fr gJ (by decide),
      r1.fr gJ (by decide), hJ]
  refine Hs.last (hs_inc C gJ b5 (by rw [b5J]; exact hJW)) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  have wS0 : ∀ m ∈ ([] : List (Fin MM)), m ∈ [sHd, sI, sR] := fun _ h => by simp at h
  have wSH : ∀ m ∈ [sHd], m ∈ [sHd, sI, sR] := fun m h => by simp at h; simp [h]
  have wSIR : ∀ m ∈ [sI, sR], m ∈ [sHd, sI, sR] := fun m h => by simp at h; rcases h with h | h <;> simp [h]
  refine ⟨⟨?_, ?_, ?_, i5, c5, e5, f5, by rw [DS.set_env_self, b5J], cst_set k5 _ (by decide)⟩, ?_⟩
  · have hr := ((((r1.weaken wE0 wS0).trans (r2.weaken wE0 wS0)).trans (r3.weaken wE wSH)).trans
      (r4.weaken wE0 wS0)).trans (r5.weaken wE wSIR) |>.set (x := gJ) (b5.env gJ + 1) List.mem_cons_self
    refine hr.eqk (by simp) ?_
    rw [hS, r1.fr gDn (by decide), hD, r3.fr gTG (by decide), b2f gTG (by decide), hTG]
    simp only [itemN, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, marksD_append,
      List.append_assoc, List.nil_append]
  · rw [DS.set_ram, r5.ram sHd (by decide), r4.ram sHd (by simp), i3]
  · rw [DS.set_rc, r5.rc sHd (by decide), r4.rc sHd (by simp), c3, hDN]
  · rw [(b4s sI (by decide)).2] at hn5
    rw [(b2s sHd).2] at hn3
    unfold itemCostG
    omega

/-! ## The items of a group -/

/-- The numbers of the gathered items of a group. -/
def itemsN (s D : ℕ) (DN IL RL : List ℕ) (PW tg nc : ℕ) : List ℕ :=
  (List.range nc).flatMap (itemN s D DN IL RL PW tg)

theorem gItemsS_spec (a : DS VV MM) (hc : Cst a) (s D : ℕ) (DN IL RL : List ℕ) (PW tg nc : ℕ) (hS : a.env gS = s)
    (hD : a.env gDn = D) (hDN : DN.length = 2 * D) (hH : a.ram sHd = DN) (hHc : a.rc sHd ≤ 2 * D)
    (hTG : a.env gTG = tg) (hI : a.ram sI = IL) (hIc : a.rc sI ≤ 3 * tg) (hIl : 3 * tg ≤ IL.length)
    (hR : a.ram sR = RL) (hRc : a.rc sR = 0) (hRl : nc * tg ≤ RL.length) (hCC : a.env gCC = nc)
    (hPW : a.env gPW = PW) (hP0 : 0 < PW) (hP2 : 2 * PW ≤ 2 ^ C.Wd) (ℓ : ℕ)
    (hv : ∀ j < nc, ∀ v ∈ itemN s D DN IL RL PW tg j, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hDW : D < 2 ^ C.Wd)
    (htg : tg < 2 ^ C.Wd) (hncW : nc < 2 ^ C.Wd) :
    Hs C gItemsS a (nc * (itemCostG ℓ D tg + 2) + 4)
      (fun b => Ran a b 0 (marksD 1 ((itemsN s D DN IL RL PW tg nc).flatMap natWord)) (gJ :: emT) [sHd, sI, sR] ∧
        b.ram sHd = DN ∧ b.rc sHd ≤ 2 * D ∧ b.ram sI = IL ∧ b.rc sI ≤ 3 * tg ∧ b.ram sR = RL ∧
        b.rc sR = nc * tg ∧ Cst b) := by
  let I : ℕ → DS VV MM → Prop := fun j b => b.env gJ = j ∧ b.env gCC = nc ∧ b.env gS = s ∧ b.env gDn = D ∧
    b.env gTG = tg ∧ b.env gPW = PW ∧ b.ram sHd = DN ∧ b.rc sHd ≤ 2 * D ∧ b.ram sI = IL ∧ b.rc sI ≤ 3 * tg ∧
    b.ram sR = RL ∧ b.rc sR = j * tg ∧
    Ran a b 0 (marksD 1 ((itemsN s D DN IL RL PW tg j).flatMap natWord)) (gJ :: emT) [sHd, sI, sR] ∧ Cst b
  have loop := loopCnt (C := C) gJ gCC (by decide) gItemS nc (itemCostG ℓ D tg) I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
    intro j hj b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    have hjt : j * tg + tg ≤ nc * tg := by
      have := Nat.mul_le_mul_right tg (show j + 1 ≤ nc by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
    refine (gItemS_spec b h14 s D DN IL RL PW tg j h3 h4 hDN h7 h8 h5 h9 h10 hIl h11 h12 (by omega) h1 h6 hP0 hP2 ℓ
      (hv j hj) hℓ hDW htg (by omega)).mono le_rfl ?_
    rintro d ⟨r1, e1, e2, e3, e4, e5, e6, e7, c1⟩
    refine ⟨e7, by rw [r1.fr gCC (by decide), h2], by rw [r1.fr gS (by decide), h3],
      by rw [r1.fr gDn (by decide), h4], by rw [r1.fr gTG (by decide), h5], by rw [r1.fr gPW (by decide), h6], e1,
      by omega, e3, by omega, e5, by rw [e6]; ring, ?_, c1⟩
    refine (h13.trans r1).eqk rfl ?_
    simp only [itemsN, List.range_succ, List.flatMap_append, List.flatMap_singleton, marksD_append])
  refine Hx.hs (Hs.then (hs_zero C gJ a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hCC], by vsimp [hS], by vsimp [hD], by vsimp [hTG], by vsimp [hPW],
    hH, hHc, hI, hIc, hR, by rw [DS.set_rc, hRc, Nat.zero_mul],
    ((Ran.refl a (gJ :: emT) [sHd, sI, sR]).set (x := gJ) 0 List.mem_cons_self).eqk rfl (by simp [itemsN, marksD]),
    cst_set hc _ (by decide)⟩)
    (fun b ⟨_, _, _, _, _, _, h7, h8, h9, h10, h11, h12, h13, h14⟩ n hn => ⟨⟨h13, h7, h8, h9, h10, h11, h12, h14⟩,
      by omega⟩)

end NearQuarticWires.Reconstruct.GatherProg
