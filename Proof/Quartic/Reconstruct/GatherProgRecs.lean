import Proof.Quartic.Reconstruct.GatherProgGroup

/-!
# The gathering program: the transposition by sorting

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

After the tables of a group, the store `sC` holds the certified counts table by table: position `i = k·n_c + j`
holds the count of the `j`-th certified column in table `k`. `recsS` writes, for every position, the record
`(j·tg + k)·PW + c` (`keyOf`, `recsK`), where `PW` exceeds every count; sorting them (`srtM`) puts them column by
column (`recsK_sort`): position `t = j·tg + k` of the sorted store holds `t·PW + c` (`recsJ`).
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

/-! ## The records and their order -/

/-- The key of position `i`: column `i % n_c`, table `i / n_c`. -/
def keyOf (tg nc i : ℕ) : ℕ := (i % nc) * tg + i / nc

/-- The count of the sorted position `t` (column `t / tg`, table `t % tg`). -/
def cntAt (tg nc : ℕ) (Cf : List ℕ) (t : ℕ) : ℕ := Cf.getD ((t % tg) * nc + t / tg) 0

/-- The records in the order of the positions. -/
def recsK (tg nc PW : ℕ) (Cf : List ℕ) : List ℕ :=
  (List.range (tg * nc)).map fun i => keyOf tg nc i * PW + Cf.getD i 0

/-- The records in the order of the keys. -/
def recsJ (tg nc PW : ℕ) (Cf : List ℕ) : List ℕ :=
  (List.range (tg * nc)).map fun t => t * PW + cntAt tg nc Cf t

theorem keyOf_lt (tg nc i : ℕ) (hi : i < tg * nc) : keyOf tg nc i < tg * nc := by
  have hnc : 0 < nc := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have h1 : i / nc < tg := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  have h2 : i % nc + 1 ≤ nc := Nat.mod_lt _ hnc
  unfold keyOf
  calc i % nc * tg + i / nc < i % nc * tg + tg := by omega
    _ = (i % nc + 1) * tg := by ring
    _ ≤ nc * tg := Nat.mul_le_mul_right _ h2
    _ = tg * nc := Nat.mul_comm _ _

theorem keyOf_mod (tg nc i : ℕ) (hi : i < tg * nc) : keyOf tg nc i % tg = i / nc := by
  have hnc : 0 < nc := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have h1 : i / nc < tg := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  unfold keyOf
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]

theorem keyOf_div (tg nc i : ℕ) (hi : i < tg * nc) : keyOf tg nc i / tg = i % nc := by
  have hnc : 0 < nc := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have htg : 0 < tg := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have h1 : i / nc < tg := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
  unfold keyOf
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ htg, Nat.div_eq_of_lt h1, Nat.zero_add]

theorem cntAt_keyOf (tg nc : ℕ) (Cf : List ℕ) (i : ℕ) (hi : i < tg * nc) :
    cntAt tg nc Cf (keyOf tg nc i) = Cf.getD i 0 := by
  unfold cntAt
  rw [keyOf_mod tg nc i hi, keyOf_div tg nc i hi, Nat.mul_comm, Nat.div_add_mod]

theorem recsK_eq (tg nc PW : ℕ) (Cf : List ℕ) :
    recsK tg nc PW Cf = ((List.range (tg * nc)).map (keyOf tg nc)).map fun t => t * PW + cntAt tg nc Cf t := by
  unfold recsK
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  simp only [Function.comp, cntAt_keyOf tg nc Cf i (List.mem_range.mp hi)]

theorem keys_perm (tg nc : ℕ) : List.Perm ((List.range (tg * nc)).map (keyOf tg nc)) (List.range (tg * nc)) := by
  have hnd : ((List.range (tg * nc)).map (keyOf tg nc)).Nodup := by
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    have hx' := List.mem_range.mp hx
    have hy' := List.mem_range.mp hy
    have e1 := keyOf_mod tg nc x hx'
    have e2 := keyOf_div tg nc x hx'
    rw [hxy, keyOf_mod tg nc y hy'] at e1
    rw [hxy, keyOf_div tg nc y hy'] at e2
    rw [← Nat.div_add_mod x nc, ← Nat.div_add_mod y nc, e1, e2]
  have hsub : (List.range (tg * nc)).map (keyOf tg nc) ⊆ List.range (tg * nc) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact List.mem_range.mpr (keyOf_lt tg nc i (List.mem_range.mp hi))
  exact (hnd.subperm hsub).perm_of_length_le (by simp)

theorem cntAt_lt (tg nc PW : ℕ) (Cf : List ℕ) (hPW : 0 < PW) (hC : ∀ x ∈ Cf, x < PW) (t : ℕ) :
    cntAt tg nc Cf t < PW := by
  unfold cntAt
  rw [List.getD_eq_getElem?_getD]
  cases h : Cf[(t % tg) * nc + t / tg]? with
  | none => simpa using hPW
  | some x => simpa using hC x (List.mem_of_getElem? h)

/-- **Sorting the records** puts them in the order of the keys. -/
theorem recsK_sort (tg nc PW : ℕ) (Cf : List ℕ) (hPW : 0 < PW) (hC : ∀ x ∈ Cf, x < PW) :
    (recsK tg nc PW Cf).insertionSort (· ≤ ·) = recsJ tg nc PW Cf := by
  have hmono : ∀ t t', t < t' → t * PW + cntAt tg nc Cf t ≤ t' * PW + cntAt tg nc Cf t' := by
    intro t t' h
    have h1 := cntAt_lt tg nc PW Cf hPW hC t
    have h2 : (t + 1) * PW ≤ t' * PW := Nat.mul_le_mul_right _ h
    have e : (t + 1) * PW = t * PW + PW := by ring
    omega
  have hsorted : (recsJ tg nc PW Cf).Pairwise (· ≤ ·) := by
    unfold recsJ
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range (n := tg * nc)).imp fun h => hmono _ _ h
  refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _) hsorted ?_
  refine (List.perm_insertionSort _ _).trans ?_
  rw [recsK_eq]
  exact (keys_perm tg nc).map _

/-! ## The records program -/

/-- One record: the count at the cursor of `sC`, its key from the position `gI`, the record onto `sR`. -/
def recS : St VV MM := .seq (.op (.rdM sC gC)) (.seq (.op (.dm gI gCC gQ gRem)) (.seq (.op (.mul gRem gTG gRec))
  (.seq (.op (.add gRec gQ)) (.seq (.op (.mul gRec gPW gT)) (.seq (.op (.add gT gC)) (.seq (.op (.wrM sR gT))
    (.op (.inc gI))))))))

/-- The records of a group. -/
def recsS : St VV MM := .seq (.op (.rwM sC)) (.seq (.op (.rwM sR)) (.seq (.op (.zero gI)) (.loop (.lt gI gNR) recS)))

/-- The variables written by `recsS`. -/
def recT : List (Fin VV) := [gC, gI, gQ, gRem, gRec, gT]

theorem recsS_spec (a : DS VV MM) (hc : Cst a) (tg nc PW : ℕ) (Cf : List ℕ) (hCf : Cf.length = tg * nc)
    (hC : a.ram sC = Cf) (oR : List ℕ) (hR : a.ram sR = oR) (hoR : oR.length ≤ tg * nc)
    (hTG : a.env gTG = tg) (hCC : a.env gCC = nc) (hPW : a.env gPW = PW) (hNR : a.env gNR = tg * nc)
    (hPW0 : 0 < PW) (hlt : ∀ x ∈ Cf, x < PW) (hW : tg * nc * PW < 2 ^ C.Wd) (hW2 : 2 * nc ≤ 2 ^ C.Wd) :
    Hs C recsS a (a.rc sC + a.rc sR + tg * nc * 18 + 8)
      (fun b => b.ram sR = recsK tg nc PW Cf ∧ b.rc sR = tg * nc ∧ b.ram sC = Cf ∧ b.rc sC = tg * nc ∧
        Ran a b 0 [] recT [sC, sR] ∧ Cst b) := by
  set N := tg * nc with hN
  let f : ℕ → ℕ := fun i => keyOf tg nc i * PW + Cf.getD i 0
  have hS : ∀ m ∈ [sC, sR], m ∈ [sC, sR] := fun _ h => h
  let I : ℕ → DS VV MM → Prop := fun i b => b.env gI = i ∧ b.env gNR = N ∧ b.env gCC = nc ∧ b.env gTG = tg ∧
    b.env gPW = PW ∧ b.ram sC = Cf ∧ b.rc sC = i ∧ b.ram sR = ovw oR ((List.range i).map f) ∧ b.rc sR = i ∧
    Ran a b 0 [] recT [sC, sR] ∧ Cst b
  have loop := loopCnt (C := C) gI gNR (by decide) recS N 16 I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
    intro i hi b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    have hnc : 0 < nc := Nat.pos_of_ne_zero (by rintro rfl; simp [hN] at hi)
    have hkey : keyOf tg nc i < N := keyOf_lt tg nc i hi
    have hci : Cf.getD i 0 < PW := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hlt _ (List.getElem_mem _)
    have hkP : (keyOf tg nc i + 1) * PW ≤ N * PW := Nat.mul_le_mul_right _ hkey
    have e1 : (keyOf tg nc i + 1) * PW = keyOf tg nc i * PW + PW := by ring
    have hk1 : keyOf tg nc i ≤ keyOf tg nc i * PW := Nat.le_mul_of_pos_right _ hPW0
    have hlen : ((List.range i).map f).length = i := by simp
    have hkv : keyOf tg nc i = i % nc * tg + i / nc := rfl
    have hN1 : N ≤ N * PW := Nat.le_mul_of_pos_right _ hPW0
    have hNW : N < 2 ^ C.Wd := lt_of_le_of_lt hN1 hW
    have hb2 : i % nc * tg + i / nc < 2 ^ C.Wd := hkv ▸ hkey.trans hNW
    have hb1 : i % nc * tg < 2 ^ C.Wd := lt_of_le_of_lt (Nat.le_add_right _ _) hb2
    have hb4 : (i % nc * tg + i / nc) * PW + Cf.getD i 0 < 2 ^ C.Wd := by
      rw [← hkv]
      calc keyOf tg nc i * PW + Cf.getD i 0 < keyOf tg nc i * PW + PW := by omega
        _ = (keyOf tg nc i + 1) * PW := e1.symm
        _ ≤ N * PW := hkP
        _ < 2 ^ C.Wd := hW
    have hb3 : (i % nc * tg + i / nc) * PW < 2 ^ C.Wd := lt_of_le_of_lt (Nat.le_add_right _ _) hb4
    refine (Hs.seq (t1 := 1) (t2 := 13) (hs_rdM C sC gC b (by rw [h6, h7, hCf]; exact hi)) (fun d1 hd1 => ?_)).mono
      (by norm_num) (fun _ h => h)
    have d1C : d1.env gC = Cf.getD i 0 := by rw [hd1, DS.adv_env, DS.set_env_self, h6, h7]
    have d1f : ∀ y, y ≠ gC → d1.env y = b.env y := fun y hy => by rw [hd1, DS.adv_env, DS.set_env_ne _ _ hy]
    refine (Hs.seq (t1 := 1) (t2 := 11) (hs_dm C gI gCC gQ gRem d1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by rw [d1f gCC (by decide), h3]; exact hnc)
      (by rw [d1f gCC (by decide), h3]; exact hW2)) (fun d2 hd2 => ?_)).mono (by norm_num) (fun _ h => h)
    have d2Q : d2.env gQ = i / nc := by
      rw [hd2, DS.set_env_ne _ _ (show gQ ≠ gRem by decide), DS.set_env_self, d1f gI (by decide),
        d1f gCC (by decide), h1, h3]
    have d2R : d2.env gRem = i % nc := by
      rw [hd2, DS.set_env_self, d1f gI (by decide), d1f gCC (by decide), h1, h3]
    have d2f : ∀ y, y ≠ gQ → y ≠ gRem → d2.env y = d1.env y := fun y h1 h2 => by
      rw [hd2, DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
    have d2T : d2.env gTG = tg := by rw [d2f gTG (by decide) (by decide), d1f gTG (by decide), h4]
    refine (Hs.seq (t1 := 1) (t2 := 9) (hs_mul C gRem gTG gRec d2 (by decide) (by decide) (by decide) (by
      rw [d2R, d2T]; exact hb1)) (fun d3 hd3 => ?_)).mono (by norm_num) (fun _ h => h)
    have d3R : d3.env gRec = i % nc * tg := by rw [hd3, DS.set_env_self, d2R, d2T]
    have d3f : ∀ y, y ≠ gRec → d3.env y = d2.env y := fun y hy => by rw [hd3, DS.set_env_ne _ _ hy]
    refine (Hs.seq (t1 := 1) (t2 := 7) (hs_add C gRec gQ d3 (by decide) (by
      rw [d3R, d3f gQ (by decide), d2Q]; exact hb2)) (fun d4 hd4 => ?_)).mono (by norm_num) (fun _ h => h)
    have d4R : d4.env gRec = i % nc * tg + i / nc := by
      rw [hd4, DS.set_env_self, d3R, d3f gQ (by decide), d2Q]
    have d4f : ∀ y, y ≠ gRec → d4.env y = d3.env y := fun y hy => by rw [hd4, DS.set_env_ne _ _ hy]
    have d4P : d4.env gPW = PW := by
      rw [d4f gPW (by decide), d3f gPW (by decide), d2f gPW (by decide) (by decide), d1f gPW (by decide), h5]
    refine (Hs.seq (t1 := 1) (t2 := 5) (hs_mul C gRec gPW gT d4 (by decide) (by decide) (by decide) (by
      rw [d4R, d4P]; exact hb3)) (fun d5 hd5 => ?_)).mono (by norm_num) (fun _ h => h)
    have d5T : d5.env gT = (i % nc * tg + i / nc) * PW := by rw [hd5, DS.set_env_self, d4R, d4P]
    have d5f : ∀ y, y ≠ gT → d5.env y = d4.env y := fun y hy => by rw [hd5, DS.set_env_ne _ _ hy]
    have d5C : d5.env gC = Cf.getD i 0 := by
      rw [d5f gC (by decide), d4f gC (by decide), d3f gC (by decide), d2f gC (by decide) (by decide), d1C]
    refine (Hs.seq (t1 := 1) (t2 := 3) (hs_add C gT gC d5 (by decide) (by rw [d5T, d5C]; exact hb4))
      (fun d6 hd6 => ?_)).mono (by norm_num) (fun _ h => h)
    have d6T : d6.env gT = keyOf tg nc i * PW + Cf.getD i 0 := by rw [hd6, DS.set_env_self, d5T, d5C, hkv]
    have d6f : ∀ y, y ≠ gT → d6.env y = d5.env y := fun y hy => by rw [hd6, DS.set_env_ne _ _ hy]
    -- the stores and the effect so far
    have r6 : Ran b d6 0 [] recT [sC, sR] := by
      rw [hd6, hd5, hd4, hd3, hd2, hd1]
      exact ((((((((Ran.refl b recT [sC, sR]).set (x := gC) _ (by decide)).adv (m := sC) (by simp)).set
        (x := gQ) _ (by decide)).set (x := gRem) _ (by decide)).set (x := gRec) _ (by decide)).set (x := gRec) _
        (by decide)).set (x := gT) _ (by decide)).set (x := gT) _ (by decide)
    have d6sR : d6.ram sR = ovw oR ((List.range i).map f) ∧ d6.rc sR = i := by
      rw [hd6, hd5, hd4, hd3, hd2, hd1]
      simp only [DS.set_ram, DS.set_rc, DS.adv_ram, DS.adv_rc_ne _ (show sR ≠ sC by decide), h8, h9]
      exact ⟨trivial, trivial⟩
    have d6sC : d6.ram sC = Cf ∧ d6.rc sC = i + 1 := by
      rw [hd6, hd5, hd4, hd3, hd2, hd1]
      simp only [DS.set_ram, DS.set_rc, DS.adv_ram, DS.adv_rc_self, h6, h7]
      exact ⟨trivial, trivial⟩
    refine (Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C sR gT d6 (by
      rw [d6sR.1, d6sR.2, ovw_length, hlen]; exact le_max_right _ _)) (fun d7 hd7 => ?_)).mono (by norm_num)
      (fun _ h => h)
    subst hd7
    have d7I : (d6.put sR (d6.env gT)).env gI = i := by
      rw [DS.put_env, d6f gI (by decide), d5f gI (by decide), d4f gI (by decide), d3f gI (by decide),
        d2f gI (by decide) (by decide), d1f gI (by decide), h1]
    refine Hs.mono (hs_inc C gI _ (by rw [d7I]; omega)) le_rfl ?_
    rintro d8 rfl
    have fr : ∀ y, y ∈ [gNR, gCC, gTG, gPW] → ((d6.put sR (d6.env gT)).set gI ((d6.put sR (d6.env gT)).env gI + 1)).env y = b.env y := by
      intro y hy
      rw [DS.set_env_ne _ _ (by revert y; decide), DS.put_env, r6.fr y (by revert y; decide)]
    refine ⟨by rw [DS.set_env_self, d7I], by rw [fr gNR (by simp), h2], by rw [fr gCC (by simp), h3],
      by rw [fr gTG (by simp), h4], by rw [fr gPW (by simp), h5], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [DS.set_ram, DS.put_ram_ne _ _ (show sC ≠ sR by decide), d6sC.1]
    · rw [DS.set_rc, DS.put_rc_ne _ _ (show sC ≠ sR by decide), d6sC.2]
    · rw [DS.set_ram, DS.put_ram_self, d6sR.1, d6sR.2, d6T]
      have hp := putAt_ovw oR ((List.range i).map f) (keyOf tg nc i * PW + Cf.getD i 0)
      rw [hlen] at hp
      rw [hp, List.range_succ, List.map_append, List.map_singleton]
    · rw [DS.set_rc, DS.put_rc_self, d6sR.2]
    · exact ((h10.trans r6).put (m := sR) _ (by simp)).set (x := gI) _ (by decide) |>.eqk rfl rfl
    · exact cst_set (cst_put (r6.cst h11 (by decide)) _ _) _ (by decide))
  refine Hx.hs (Hs.then (hs_rwM C sC a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_rwM C sR _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_zero C gI _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hNR], by vsimp [hCC], by vsimp [hTG], by vsimp [hPW],
    by simp only [DS.set_ram, DS.rew_ram, hC], by rw [DS.set_rc, DS.rew_rc_ne _ (show sC ≠ sR by decide),
      DS.rew_rc_self], by simp only [DS.set_ram, DS.rew_ram, hR, List.range_zero, List.map_nil, ovw_nil],
    by rw [DS.set_rc, DS.rew_rc_self],
    (((Ran.refl a recT [sC, sR]).rew (m := sC) (by simp)).rew (m := sR) (by simp)).set (x := gI) 0 (by decide),
    cst_set (cst_rew (cst_rew hc _) _) _ (by decide)⟩)
    (fun b ⟨_, _, _, _, _, h6, h7, h8, h9, h10, h11⟩ n hn => ⟨⟨?_, h9, h6, h7, h10, h11⟩, ?_⟩)
  · rw [h8]
    exact ovw_of_le _ _ (by simp; omega)
  · rw [DS.rew_rc_ne _ (show sR ≠ sC by decide)] at hn1
    omega

end NearQuarticWires.Reconstruct.GatherProg
