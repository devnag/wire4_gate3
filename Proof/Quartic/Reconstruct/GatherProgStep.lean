import Proof.Quartic.Reconstruct.GatherProgEmit

/-!
# The gathering program: one group

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`groupS` reads the tables of a group (`tablesLoopS`), sets `PW = 1 + Σ c`, writes the records (`recsS`), sorts them
and, when `κ_σ ≠ 0` (an even number of `true` pattern bits), writes the gathered items (`gItemsS`). `groupS_spec`:
the output grows by the items of the group (`grpOut`), and the stores keep the sizes the next group needs.
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

/-- **One group of tables.** -/
def groupS : St VV MM := .seq (.op (.rwM sI)) (.seq (.op (.rwM sC)) (.seq (.op (.zero gSum)) (.seq tablesLoopS
  (.seq (.op (.copy gPW gSum)) (.seq (.op (.inc gPW)) (.seq (.op (.mul gTG gCC gNR)) (.seq recsS
  (.seq (.op (.rwM sR)) (.seq (.op (.srtM sR)) (.seq (.ite (.eq gAct vZ) gItemsS skipS) (.op (.inc gGI))))))))))))

/-- The variables written by `groupS`. -/
def stepT : List (Fin VV) := [gGI, gPW, gNR, gJ, gC, gI, gRem, gRec, gT, t5, t6, t7, t8, t9, gTk, gS, gN, gK, gPar,
  gAct, gQ, gP, gDn, gZ, gSg, gB, gSum, t0, t1, t2, t3, t4, vJ]

/-- The stores written by `groupS`. -/
def stepM : List (Fin MM) := [sZc, sHd, sI, sC, sR]

/-- The certified counts of a group, table by table. -/
def cfOf (g : GrpD) (bits : List ℕ) : List ℕ := g.rows.flatMap (cntsOf bits)

/-- The record base of a group. -/
def pwOf (g : GrpD) (bits : List ℕ) : ℕ := (cfOf g bits).sum + 1

/-- **The output of a group**: its gathered items when the parity of its pattern is even. -/
def grpOut (g : GrpD) (bits : List ℕ) : List ℕ :=
  if g.pat.sum % 2 = 0 then
    itemsN g.s g.dl.length (g.dl.flatMap intNats) (g.rows.flatMap rowI)
      (recsJ g.rows.length (ncOf bits) (pwOf g bits) (cfOf g bits)) (pwOf g bits) g.rows.length (ncOf bits)
  else []

/-- The cost of one group. -/
def grpCost (ℓ : ℕ) (g : GrpD) (bits : List ℕ) : ℕ :=
  g.rows.length * (tblCostU ℓ g.pat.length g.dl.length bits.length + 4) +
    ncOf bits * (itemCostG ℓ g.dl.length g.rows.length + 2) + 3 * g.rows.length +
    25 * (g.rows.length * ncOf bits) + 60

theorem recsK_length (tg nc PW : ℕ) (Cf : List ℕ) : (recsK tg nc PW Cf).length = tg * nc := by simp [recsK]
theorem recsJ_length (tg nc PW : ℕ) (Cf : List ℕ) : (recsJ tg nc PW Cf).length = tg * nc := by simp [recsJ]


theorem getD_bits (L : List ℕ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h : ∀ x ∈ L, natBitLength x ≤ ℓ) (i : ℕ) :
    natBitLength (L.getD i 0) ≤ ℓ := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : L[i]? with
  | none =>
    rw [Option.getD_none]
    have : natBitLength 0 = 1 := by simp [natBitLength]
    omega
  | some x => exact h x (List.mem_of_getElem? hx)

theorem recsJ_getD_mod (tg nc PW : ℕ) (Cf : List ℕ) (hPW0 : 0 < PW) (hC : ∀ x ∈ Cf, x < PW) (t : ℕ)
    (ht : t < tg * nc) : (recsJ tg nc PW Cf).getD t 0 % PW = cntAt tg nc Cf t := by
  unfold recsJ
  rw [List.getD_eq_getElem _ _ (by simp; exact ht)]
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (cntAt_lt tg nc PW Cf hPW0 hC t)]

theorem recsJ_mod_bits (tg nc PW : ℕ) (Cf : List ℕ) (hPW0 : 0 < PW) (hC : ∀ x ∈ Cf, x < PW) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hb : ∀ x ∈ Cf, natBitLength x ≤ ℓ) (t : ℕ) : natBitLength ((recsJ tg nc PW Cf).getD t 0 % PW) ≤ ℓ := by
  by_cases ht : t < tg * nc
  · rw [recsJ_getD_mod tg nc PW Cf hPW0 hC t ht]; exact getD_bits Cf ℓ h1 hb _
  · rw [List.getD_eq_default _ _ (by simp [recsJ]; omega), Nat.zero_mod]; simp [natBitLength]; omega

theorem itemN_bits (s D : ℕ) (DN IL RL : List ℕ) (PW tg j ℓ : ℕ) (h2 : 2 ≤ ℓ) (hs : natBitLength s ≤ ℓ)
    (hD : natBitLength D ≤ ℓ) (hDN : ∀ x ∈ DN, natBitLength x ≤ ℓ) (htg : natBitLength tg ≤ ℓ)
    (hIL : ∀ x ∈ IL, natBitLength x ≤ ℓ) (hRL : ∀ t, natBitLength (RL.getD t 0 % PW) ≤ ℓ) :
    ∀ v ∈ itemN s D DN IL RL PW tg j, natBitLength v ≤ ℓ := by
  intro v hv
  simp only [itemN, rowsN, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hv
  rcases hv with (((h | h) | h) | h) | ⟨k, -, hk⟩
  · rw [h]; exact hs
  · rw [h]; exact hD
  · exact hDN v h
  · rw [h]; exact htg
  · simp only [rowN, List.mem_cons, List.not_mem_nil, or_false] at hk
    have h1 : 1 ≤ ℓ := by omega
    rcases hk with h | h | h | h | h <;> rw [h]
    · exact getD_bits IL ℓ h1 hIL _
    · have : natBitLength 2 = 2 := by decide
      omega
    · exact getD_bits IL ℓ h1 hIL _
    · exact getD_bits IL ℓ h1 hIL _
    · exact hRL _

theorem mem_nats (g : GrpD) (r : RowD) (hr : r ∈ g.rows) (v : ℕ) (hv : v ∈ tblNats (g.tbl r)) : v ∈ g.nats :=
  List.mem_flatMap.mpr ⟨r, hr, hv⟩

theorem groupS_spec (a : DS VV MM) (hc : Cst a) (g : GrpD) (bits vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (g.nats ++ vs).flatMap natWord ++ rest) (hne : g.rows ≠ [])
    (hTG : a.env gTG = g.rows.length) (hCC : a.env gCC = ncOf bits) (gi : ℕ) (hGI : a.env gGI = gi)
    (hZ : a.ram sZc = bits) (hZc : a.rc sZc ≤ bits.length) (hbl : ∀ r ∈ g.rows, r.2.2.2.length = bits.length)
    (hHd : (a.ram sHd).length ≤ 2 * g.dl.length) (hHdc : a.rc sHd ≤ 2 * g.dl.length)
    (hIl : (a.ram sI).length ≤ 3 * g.rows.length) (hIc : a.rc sI ≤ 3 * g.rows.length)
    (hCl : (a.ram sC).length ≤ g.rows.length * ncOf bits) (hCc : a.rc sC ≤ g.rows.length * ncOf bits)
    (hRl : (a.ram sR).length ≤ g.rows.length * ncOf bits) (hRc : a.rc sR ≤ g.rows.length * ncOf bits)
    (ℓ : ℕ) (h2ℓ : 2 ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hv : ∀ v ∈ g.nats, natBitLength v ≤ ℓ)
    (hvC : ∀ x ∈ cfOf g bits, natBitLength x ≤ ℓ) (hvT : natBitLength g.rows.length ≤ ℓ)
    (hW : g.rows.length * ncOf bits * pwOf g bits < 2 ^ C.Wd) (hWn : 2 * ncOf bits ≤ 2 ^ C.Wd)
    (hWp : 2 * pwOf g bits ≤ 2 ^ C.Wd)
    (hpat : g.pat.sum + g.pat.length < 2 ^ C.Wd) (hdl : g.dl.length < 2 ^ C.Wd) (htg : g.rows.length < 2 ^ C.Wd)
    (hnc : ncOf bits < 2 ^ C.Wd) (hgi : gi + 1 < 2 ^ C.Wd) :
    Hs C groupS a (grpCost ℓ g bits)
      (fun b => Ran a b (g.nats.flatMap natWord).length (marksD 1 ((grpOut g bits).flatMap natWord)) stepT stepM ∧
        b.env gGI = gi + 1 ∧ b.ram sZc = bits ∧ b.rc sZc ≤ bits.length ∧ (b.ram sHd).length ≤ 2 * g.dl.length ∧
        b.rc sHd ≤ 2 * g.dl.length ∧ (b.ram sI).length ≤ 3 * g.rows.length ∧ b.rc sI ≤ 3 * g.rows.length ∧
        (b.ram sC).length ≤ g.rows.length * ncOf bits ∧ b.rc sC ≤ g.rows.length * ncOf bits ∧
        (b.ram sR).length ≤ g.rows.length * ncOf bits ∧ b.rc sR ≤ g.rows.length * ncOf bits ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hCfl : (cfOf g bits).length = g.rows.length * ncOf bits := by
    rw [cfOf, cntsOf_flatMap_length bits g.rows hbl, Nat.mul_comm]
  have hPW0 : 0 < pwOf g bits := by unfold pwOf; omega
  have hCfs : (g.rows.flatMap (cntsOf bits)).sum < 2 ^ C.Wd := by
    have : 2 * ((cfOf g bits).sum + 1) ≤ 2 ^ C.Wd := hWp
    unfold cfOf at this; omega
  have hCPW : ∀ x ∈ cfOf g bits, x < pwOf g bits := fun x hx => by
    unfold pwOf; have := List.le_sum_of_mem hx; omega
  have hNW : g.rows.length * ncOf bits < 2 ^ C.Wd := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hPW0) hW
  -- the tables
  refine Hx.hs (Hs.then (hs_rwM C sI a) (fun b1 hb1 n1 hn1 => ?_))
  subst hb1
  refine Hs.then (hs_rwM C sC _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  refine Hs.then (hs_zero C gSum _) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (tablesLoopS_spec _ (cst_set (cst_rew (cst_rew hc _) _) _ (by decide)) g bits vs rest
    (by simpa using hin) hne (by vsimp [hTG]) (by simp [hZ]) (by simp [DS.rew_rc_ne _ (show sZc ≠ sC by decide),
      DS.rew_rc_ne _ (show sZc ≠ sI by decide), hZc]) hbl (by simpa using hHd)
    (by simp [DS.rew_rc_ne _ (show sHd ≠ sC by decide), DS.rew_rc_ne _ (show sHd ≠ sI by decide), hHdc])
    (a.ram sI) rfl (by simp [DS.rew_rc_ne _ (show sI ≠ sC by decide)]) (a.ram sC) rfl (by simp) (by vsimp [])
    ℓ hv hℓ hCfs hpat hdl htg) (fun b4 ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, r4, c4, i4⟩ n4 hn4 => ?_)
  -- the record base and the number of records
  refine Hs.then (hs_copy C gPW gSum b4 (by decide)) (fun b5 hb5 n5 hn5 => ?_)
  have b5P : b5.env gPW = (cfOf g bits).sum := by rw [hb5, DS.set_env_self, e5]; rfl
  have b5f : ∀ y, y ≠ gPW → b5.env y = b4.env y := fun y hy => by rw [hb5, DS.set_env_ne _ _ hy]
  refine Hs.then (hs_inc C gPW b5 (by rw [b5P]; unfold pwOf at hWp; omega)) (fun b6 hb6 n6 hn6 => ?_)
  have b6P : b6.env gPW = pwOf g bits := by rw [hb6, DS.set_env_self, b5P]; rfl
  have b6f : ∀ y, y ≠ gPW → b6.env y = b4.env y := fun y hy => by rw [hb6, DS.set_env_ne _ _ hy, b5f y hy]
  have b6TG : b6.env gTG = g.rows.length := by rw [b6f gTG (by decide), e4]
  have b6CC : b6.env gCC = ncOf bits := by rw [b6f gCC (by decide), r4.fr gCC (by decide)]; vsimp [hCC]
  refine Hs.then (hs_mul C gTG gCC gNR b6 (by decide) (by decide) (by decide) (by rw [b6TG, b6CC]; exact hNW))
    (fun b7 hb7 n7 hn7 => ?_)
  have b7f : ∀ y, y ≠ gNR → b7.env y = b6.env y := fun y hy => by rw [hb7, DS.set_env_ne _ _ hy]
  have b7NR : b7.env gNR = g.rows.length * ncOf bits := by rw [hb7, DS.set_env_self, b6TG, b6CC]
  have r7 : Ran b4 b7 0 [] [gPW, gNR] [] := by
    rw [hb7, hb6, hb5]
    exact (((Ran.refl b4 [gPW, gNR] []).set _ (by simp)).set _ (by simp)).set _ (by simp)
  have b7s : ∀ m : Fin MM, b7.ram m = b4.ram m ∧ b7.rc m = b4.rc m := fun m =>
    ⟨r7.ram m (by simp), r7.rc m (by simp)⟩
  have c7 : Cst b7 := r7.cst c4 (by decide)
  -- the records
  have b7C : b7.ram sC = cfOf g bits := by
    rw [(b7s sC).1, e10]; exact ovw_of_le _ _ (hCl.trans hCfl.symm.le)
  refine Hs.then (recsS_spec b7 c7 g.rows.length (ncOf bits) (pwOf g bits) (cfOf g bits) hCfl b7C (a.ram sR)
    (by rw [(b7s sR).1, r4.ram sR (by decide)]; simp) hRl (by rw [b7f gTG (by decide), b6TG])
    (by rw [b7f gCC (by decide), b6CC]) (by rw [b7f gPW (by decide), b6P]) b7NR hPW0 hCPW hW hWn)
    (fun b8 ⟨f1, f2, f3, f4, r8, c8⟩ n8 hn8 => ?_)
  -- the sort
  refine Hs.then (hs_rwM C sR b8) (fun b9 hb9 n9 hn9 => ?_)
  subst hb9
  refine Hs.then (hs_srtM C sR _ (by simp)) (fun b10 hb10 n10 hn10 => ?_)
  subst hb10
  have b10R : ((b8.rew sR).srt sR).ram sR = recsJ g.rows.length (ncOf bits) (pwOf g bits) (cfOf g bits) := by
    rw [DS.srt_ram_self, DS.rew_ram, f1, recsK_sort _ _ _ _ hPW0 hCPW]
  set b10 := (b8.rew sR).srt sR with hb10
  have r10 : Ran b4 b10 0 [] (recT ++ [gPW, gNR]) [sC, sR] := by
    have := (r7.weaken (T' := recT ++ [gPW, gNR]) (S' := [sC, sR]) (fun y hy => by revert y; decide)
      (fun _ h => by simp at h)).trans (r8.weaken (T' := recT ++ [gPW, gNR]) (fun y hy => by revert y; decide)
      (fun _ h => h))
    exact ((this.rew (m := sR) (by simp)).srt (m := sR) (by simp)).eqk rfl rfl
  have c10 : Cst b10 := r10.cst c4 (by decide)
  have hrow : g.rows ≠ [] := hne
  obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hrow
  have hnat : ∀ v ∈ tblNats (g.tbl r0), natBitLength v ≤ ℓ := fun v h => hv v (mem_nats g r0 hr0 v h)
  have hDNb : ∀ x ∈ g.dl.flatMap intNats, natBitLength x ≤ ℓ := fun x h => hnat x (by
    simp only [tblNats, GrpD.tbl, List.mem_append]; tauto)
  have hILb : ∀ x ∈ g.rows.flatMap rowI, natBitLength x ≤ ℓ := by
    intro x hx
    obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
    have hn : ∀ v ∈ tblNats (g.tbl r), natBitLength v ≤ ℓ := fun v h => hv v (mem_nats g r hr v h)
    simp only [rowI, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h <;> rw [h] <;> refine hn _ ?_ <;> simp [tblNats, GrpD.tbl, intNats]
  have b10S : b10.env gS = g.s := by rw [r10.fr gS (by decide), e1]
  have b10A : b10.env gAct = g.pat.sum % 2 := by rw [r10.fr gAct (by decide), e2]
  have b10D : b10.env gDn = g.dl.length := by rw [r10.fr gDn (by decide), e3]
  have b10T : b10.env gTG = g.rows.length := by rw [r10.fr gTG (by decide), e4]
  have b10C : b10.env gCC = ncOf bits := by rw [r10.fr gCC (by decide), r4.fr gCC (by decide)]; vsimp [hCC]
  have b10P : b10.env gPW = pwOf g bits := by
    rw [hb10, DS.srt_env, DS.rew_env, r8.fr gPW (by decide), b7f gPW (by decide), b6P]
  have b10H : b10.ram sHd = g.dl.flatMap intNats ∧ b10.rc sHd = 2 * g.dl.length := ⟨by
    rw [r10.ram sHd (by decide), e6], by rw [r10.rc sHd (by decide), e7]⟩
  have hILl : (g.rows.flatMap rowI).length = 3 * g.rows.length := rowI_flatMap_length _
  have b10I : b10.ram sI = g.rows.flatMap rowI ∧ b10.rc sI = 3 * g.rows.length := ⟨by
    rw [r10.ram sI (by decide), e8]; exact ovw_of_le _ _ (by rw [hILl]; exact hIl),
    by rw [r10.rc sI (by decide), e9, hILl]⟩
  have b10R0 : b10.rc sR = 0 := by rw [hb10, DS.srt_rc, DS.rew_rc_self]
  have hRJl := recsJ_length g.rows.length (ncOf bits) (pwOf g bits) (cfOf g bits)
  -- the items
  let Q : DS VV MM → Prop := fun b =>
    Ran b10 b 0 (marksD 1 ((grpOut g bits).flatMap natWord)) (gJ :: emT) [sHd, sI, sR] ∧
      b.ram sHd = g.dl.flatMap intNats ∧ b.rc sHd ≤ 2 * g.dl.length ∧ b.ram sI = g.rows.flatMap rowI ∧
      b.rc sI ≤ 3 * g.rows.length ∧ b.ram sR = recsJ g.rows.length (ncOf bits) (pwOf g bits) (cfOf g bits) ∧
      b.rc sR ≤ g.rows.length * ncOf bits ∧ Cst b
  have hite : Hs C (.ite (.eq gAct vZ) gItemsS skipS) b10
      (ncOf bits * (itemCostG ℓ g.dl.length g.rows.length + 2) + 5) Q := by
    refine Hs.ite (c := .eq gAct vZ) (show gAct ≠ vZ by decide) (fun he => ?_) (fun he => ?_)
    · have hpar : g.pat.sum % 2 = 0 := by simpa [Cnd.eval, b10A, c10.z] using he
      refine (gItemsS_spec b10 c10 g.s g.dl.length (g.dl.flatMap intNats) (g.rows.flatMap rowI)
        (recsJ g.rows.length (ncOf bits) (pwOf g bits) (cfOf g bits)) (pwOf g bits) g.rows.length (ncOf bits)
        b10S b10D (intNats_flatMap_length _) b10H.1 b10H.2.le b10T b10I.1 b10I.2.le hILl.ge b10R b10R0
        (by rw [hRJl, Nat.mul_comm]) b10C b10P hPW0 hWp ℓ (fun j _ => itemN_bits _ _ _ _ _ _ _ _ ℓ h2ℓ
          (hnat _ (by simp [tblNats, GrpD.tbl])) (hnat _ (by simp [tblNats, GrpD.tbl])) hDNb hvT hILb
          (recsJ_mod_bits _ _ _ _ hPW0 hCPW ℓ (by omega) hvC)) hℓ hdl htg hnc).mono (by omega) ?_
      rintro b ⟨r, h1, h2, h3, h4, h5, h6, cb⟩
      refine ⟨r.eqk rfl (by rw [grpOut, if_pos hpar]), h1, h2, h3, h4, h5, by rw [h6, Nat.mul_comm], cb⟩
    · have hpar : g.pat.sum % 2 ≠ 0 := by intro h; simp [Cnd.eval, b10A, c10.z, h] at he
      refine (skip_spec b10).mono (by omega) ?_
      rintro b rfl
      refine ⟨((Ran.refl b10 _ _).set 0 (by decide)).eqk rfl (by rw [grpOut, if_neg hpar]; simp [marksD]),
        b10H.1, b10H.2.le, b10I.1, b10I.2.le, b10R, by rw [DS.set_rc, b10R0]; omega, cst_set c10 _ (by decide)⟩
  refine Hs.then hite (fun b11 ⟨r11, q1, q2, q3, q4, q5, q6, c11⟩ n11 hn11 => ?_)
  have b11G : b11.env gGI = gi := by
    rw [r11.fr gGI (by decide), r10.fr gGI (by decide), r4.fr gGI (by decide)]; vsimp [hGI]
  refine Hs.last (hs_inc C gGI b11 (by rw [b11G]; exact hgi)) (fun b12 hb12 n12 hn12 => ?_)
  subst hb12
  have hsS : ∀ m ∈ ([] : List (Fin MM)), m ∈ stepM := fun _ h => by simp at h
  have r3 : Ran a ((((a.rew sI).rew sC).set gSum 0)) 0 [] stepT stepM :=
    ((((Ran.refl a stepT stepM).rew (m := sI) (by decide)).rew (m := sC) (by decide)).set (x := gSum) 0 (by decide))
  refine ⟨⟨?_, by rw [DS.set_env_self, b11G], ?_, ?_, ?_, q2, by rw [DS.set_ram, q3, hILl], q4, ?_, ?_, ?_, q6,
    cst_set c11 _ (by decide), ?_⟩, ?_⟩
  · have hr := (((r3.trans (r4.weaken (fun y hy => by revert y; decide) (fun m h => by revert m; decide))).trans
      (r10.weaken (fun y hy => by revert y; decide) (fun m h => by revert m; decide))).trans
      (r11.weaken (fun y hy => by revert y; decide) (fun m h => by revert m; decide))).set (x := gGI)
      (b11.env gGI + 1) (by decide)
    exact hr.eqk (by simp) (by simp)
  · rw [DS.set_ram, r11.ram sZc (by decide), r10.ram sZc (by decide), e12]
  · rw [DS.set_rc, r11.rc sZc (by decide), r10.rc sZc (by decide), e13]
  · rw [DS.set_ram, q1, intNats_flatMap_length]
  · rw [DS.set_ram, r11.ram sC (by decide), hb10, DS.srt_ram_ne _ (show sC ≠ sR by decide), DS.rew_ram, f3, hCfl]
  · rw [DS.set_rc, r11.rc sC (by decide), hb10, DS.srt_rc, DS.rew_rc_ne _ (show sC ≠ sR by decide), f4]
  · rw [DS.set_ram, q5, hRJl]
  · simp only [DS.set_ip, r11.ip, r10.ip, Nat.add_zero]; exact i4
  · have hc8 : b7.rc sC = (g.rows.flatMap (cntsOf bits)).length := by rw [(b7s sC).2, e11]
    have hr8 : b7.rc sR = a.rc sR := by
      rw [(b7s sR).2, r4.rc sR (by decide)]
      simp only [DS.set_rc, DS.rew_rc_ne _ (show sR ≠ sC by decide), DS.rew_rc_ne _ (show sR ≠ sI by decide)]
    rw [hc8, hr8] at hn8
    simp only [DS.rew_rc_ne _ (show sC ≠ sI by decide)] at hn2
    rw [f2] at hn9
    rw [DS.rew_ram, f1, recsK_length] at hn10
    rw [cntsOf_flatMap_length bits g.rows hbl] at hn8
    unfold grpCost
    have e : ncOf bits * g.rows.length = g.rows.length * ncOf bits := Nat.mul_comm _ _
    omega

end NearQuarticWires.Reconstruct.GatherProg
