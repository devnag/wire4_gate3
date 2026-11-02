import Proof.Quartic.Reconstruct.GatherProgBase

/-!
# The gathering program: reading one printed table

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

A printed table is its index word `(s, σ, p, δ, ρ_Y)` (`Greedy.printIndexWord`) and its entries, all numbers
(`tblNats`). `tableS` reads it: the part into `gS`, the parity of the pattern into `gAct` (`patS`), the prime into
`gP`, the digits into the store `sHd` (`dS`), the row `(p, |ρ_1|, |ρ_2|)` onto the store `sI` (`rhoS`), and the counts
of the certified columns onto the store `sC`, adding them to `gSum` (`entsS`). This file proves the parts.
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

/-! ## The data of a table -/

/-- The two numbers of an integer in `intWord`: its sign and its magnitude. -/
def intNats (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

theorem intWord_eq_nats (z : ℤ) : NearCubicGates.Close.Interfaces.intWord z = (intNats z).flatMap natWord := by
  simp [intNats, NearCubicGates.Close.Interfaces.intWord]

/-- The data of a printed table as the program reads it: the part, the pattern bits, the prime, the digits, the
residues and the entries. -/
structure TblD where
  s : ℕ
  pat : List ℕ
  p : ℕ
  dl : List ℤ
  r0 : ℤ
  r1 : ℤ
  ents : List ℤ

/-- The numbers of a printed table. -/
def tblNats (d : TblD) : List ℕ :=
  [d.s, d.pat.length] ++ d.pat ++ [d.p, d.dl.length] ++ d.dl.flatMap intNats ++ [2] ++ intNats d.r0 ++
    intNats d.r1 ++ [d.ents.length] ++ d.ents.flatMap intNats

/-- The counts of the certified columns (bit `1`): the entries, negative ones read as `0`. -/
def cnts (ents : List ℤ) (bits : List ℕ) : List ℕ :=
  (ents.zip bits).filterMap fun eb => if eb.2 = 1 then some eb.1.toNat else none

theorem cnts_take_succ (ents : List ℤ) (bits : List ℕ) (z : ℕ) (hz : z < ents.length) (hb : z < bits.length) :
    cnts (ents.take (z + 1)) (bits.take (z + 1)) =
      cnts (ents.take z) (bits.take z) ++ (if bits[z] = 1 then [ents[z].toNat] else []) := by
  unfold cnts
  rw [List.take_succ_eq_append_getElem hz, List.take_succ_eq_append_getElem hb,
    List.zip_append (by simp; omega), List.filterMap_append]
  congr 1
  simp only [List.zip_cons_cons, List.zip_nil_left, List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> rfl

theorem toNat_of_nats (e : ℤ) : (if (if e < 0 then 1 else 0) = 1 then 0 else e.natAbs) = e.toNat := by
  by_cases h : e < 0
  · rw [if_pos h, if_pos rfl]; omega
  · rw [if_neg h, if_neg (by norm_num)]; omega

/-! ## The program -/

/-- Add `gN` numbers into `gPar`. -/
def patS : St VV MM := .seq (.op (.zero gPar)) (.seq (.op (.zero gK))
  (.loop (.lt gK gN) (.seq rdNatI (.seq (.op (.add gPar t3)) (.op (.inc gK))))))

/-- Load `gDn` integers (two numbers each) into the store `sHd`. -/
def dS : St VV MM := .seq (.op (.rwM sHd)) (.seq (.op (.zero gK))
  (.loop (.lt gK gDn) (.seq rdNatI (.seq (.op (.wrM sHd t3)) (.seq rdNatI (.seq (.op (.wrM sHd t3))
    (.op (.inc gK))))))))

/-- Append `p` and the magnitudes of `ρ_Y` onto the store `sI`. -/
def rhoS : St VV MM := .seq (.op (.wrM sI gP)) (.seq rdNatI (.seq rdNatI (.seq rdNatI (.seq (.op (.wrM sI t3))
  (.seq rdNatI (.seq rdNatI (.op (.wrM sI t3))))))))

/-- One entry: if its column is certified, append its count onto `sC` and add it to `gSum`. -/
def entS : St VV MM := .seq (rdTo gSg) (.seq rdNatI (.seq (.op (.rdM sZc gB))
  (.seq (.ite (.eq gB v1) (.seq (.ite (.eq gSg v1) (.op (.zero t3)) skipS) (.seq (.op (.wrM sC t3))
    (.op (.add gSum t3)))) skipS) (.op (.inc gZ)))))

/-- The entries of a table. -/
def entsS : St VV MM := .seq (rdTo gN) (.seq (.op (.rwM sZc)) (.seq (.op (.zero gZ)) (.loop (.lt gZ gN) entS)))

/-- **One printed table.** -/
def tableS : St VV MM := .seq (rdTo gS) (.seq (rdTo gN) (.seq patS (.seq (.op (.dm gPar v2 gQ gAct))
  (.seq (rdTo gP) (.seq (rdTo gDn) (.seq dS (.seq rhoS entsS)))))))

/-- The variables written by `tableS`. -/
def tblT : List (Fin VV) := [gS, gN, gK, gPar, gAct, gQ, gP, gDn, gZ, gSg, gB, gSum, t0, t1, t2, t3, t4, vJ]

/-- The stores written by `tableS`. -/
def tblM : List (Fin MM) := [sZc, sHd, sI, sC]

/-! ## The pattern -/

theorem patS_spec (a : DS VV MM) (hc : Cst a) (pat vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (pat ++ vs).flatMap natWord ++ rest) (hN : a.env gN = pat.length) (ℓ : ℕ)
    (hv : ∀ v ∈ pat, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hs : pat.sum + pat.length < 2 ^ C.Wd) :
    Hs C patS a (pat.length * (unitC ℓ + 2) + 8)
      (fun b => b.env gPar = pat.sum ∧ b.env gN = pat.length ∧
        Ran a b (pat.flatMap natWord).length [] (gPar :: gK :: rdNatT) [] ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hT : vZ ∉ gPar :: gK :: rdNatT ∧ v1 ∉ gPar :: gK :: rdNatT ∧ v2 ∉ gPar :: gK :: rdNatT := by decide
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gK = k ∧ b.env gN = pat.length ∧ b.env gPar = (pat.take k).sum ∧
    Ran a b ((pat.take k).flatMap natWord).length [] (gPar :: gK :: rdNatT) [] ∧ Cst b ∧
    C.inp.drop b.ip = (pat.drop k ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) gK gN (by decide) (.seq rdNatI (.seq (.op (.add gPar t3)) (.op (.inc gK))))
    pat.length (unitC ℓ) I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6⟩
      have hk' : pat.drop k = pat[k] :: pat.drop (k + 1) := List.drop_eq_getElem_cons hk
      rw [hk', List.cons_append] at h6
      refine (Hs.seq (t2 := 3) (rdN_spec b h5 pat[k] _ rest h6 ℓ (hv _ (List.getElem_mem hk)) hℓ)
        (fun d ⟨e1, e2, e3, e4⟩ => ?_)).mono (t' := unitC ℓ) (by unfold unitC; omega) (fun _ h => h)
      have dK : d.env gK = k := by rw [e2.fr gK (by decide), h1]
      have dN : d.env gN = pat.length := by rw [e2.fr gN (by decide), h2]
      have dP : d.env gPar = (pat.take k).sum := by rw [e2.fr gPar (by decide), h3]
      have hsk : (pat.take (k + 1)).sum = (pat.take k).sum + pat[k] := by
        rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      have hsle : (pat.take (k + 1)).sum ≤ pat.sum := List.Sublist.sum_le_sum (List.take_sublist _ _)
        (fun _ _ => Nat.zero_le _)
      refine (Hs.seq (t1 := 1) (t2 := 1) (hs_add C gPar t3 d (by decide) (by rw [dP, e1]; omega))
        (fun f hf => ?_)).mono (by norm_num) (fun _ h => h)
      subst hf
      refine Hs.mono (hs_inc C gK _ (by vsimp [dK]; omega)) le_rfl ?_
      rintro g rfl
      refine ⟨by vsimp [dK], by vsimp [dN], by vsimp [dP, e1, hsk], ?_, ?_, ?_⟩
      · have hr := (h4.trans (e2.weaken (fun y hy => by simp only [List.mem_cons]; tauto) (fun _ h => h))).set
          (x := gPar) (d.env gPar + d.env t3) (by decide) |>.set (x := gK)
          ((d.set gPar (d.env gPar + d.env t3)).env gK + 1) (by decide)
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton, List.length_append]
        simpa using hr
      · exact cst_set (cst_set e3 _ (by decide)) _ (by decide)
      · simpa using e4)
  refine Hx.hs (Hs.then (hs_zero C gPar a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C gK _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hN], by vsimp [], ?_, cst_set (cst_set hc _ (by decide)) _ (by decide),
    by simpa using hin⟩) (fun b ⟨_, h2, h3, h4, h5, h6⟩ n hn => ⟨⟨?_, h2, ?_, h5, ?_⟩, ?_⟩)
  · exact (((Ran.refl a _ []).set 0 (by decide)).set 0 (by decide))
  · rw [h3, List.take_length]
  · simpa [List.take_length] using h4
  · simpa using h6
  · omega

/-! ## The digits -/

theorem intNats_flatMap_length (l : List ℤ) : (l.flatMap intNats).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons z l ih => simp [intNats, ih]; omega

theorem dS_spec (a : DS VV MM) (hc : Cst a) (dl : List ℤ) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (dl.flatMap intNats ++ vs).flatMap natWord ++ rest) (hN : a.env gDn = dl.length)
    (hold : (a.ram sHd).length ≤ 2 * dl.length) (ℓ : ℕ)
    (hv : ∀ v ∈ dl.flatMap intNats, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hn : dl.length < 2 ^ C.Wd) :
    Hs C dS a (a.rc sHd + dl.length * (2 * unitC ℓ + 2) + 8)
      (fun b => b.ram sHd = dl.flatMap intNats ∧ b.rc sHd = 2 * dl.length ∧ b.env gDn = dl.length ∧
        Ran a b ((dl.flatMap intNats).flatMap natWord).length [] (gK :: rdNatT) [sHd] ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  set old := a.ram sHd with hold'
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gK = k ∧ b.env gDn = dl.length ∧
    b.ram sHd = ovw old ((dl.take k).flatMap intNats) ∧ b.rc sHd = 2 * k ∧
    Ran a b (((dl.take k).flatMap intNats).flatMap natWord).length [] (gK :: rdNatT) [sHd] ∧ Cst b ∧
    C.inp.drop b.ip = ((dl.drop k).flatMap intNats ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) gK gDn (by decide) (.seq rdNatI (.seq (.op (.wrM sHd t3)) (.seq rdNatI
    (.seq (.op (.wrM sHd t3)) (.op (.inc gK)))))) dl.length (2 * unitC ℓ) I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7⟩
      have hk' : dl.drop k = dl[k] :: dl.drop (k + 1) := List.drop_eq_getElem_cons hk
      have hin1 : C.inp.drop b.ip = ((if dl[k] < 0 then 1 else 0) ::
          (dl[k].natAbs :: ((dl.drop (k + 1)).flatMap intNats ++ vs))).flatMap natWord ++ rest := by
        rw [h7, hk', List.flatMap_cons]; simp [intNats]
      have hvk : ∀ v ∈ intNats dl[k], natBitLength v ≤ ℓ := fun v hv' =>
        hv v (List.mem_flatMap.mpr ⟨dl[k], List.getElem_mem hk, hv'⟩)
      have hW : (dl.take k).flatMap intNats = (dl.take k).flatMap intNats := rfl
      have hWl : ((dl.take k).flatMap intNats).length = 2 * k := by
        rw [intNats_flatMap_length, List.length_take]; omega
      refine (Hs.seq (t1 := 30 * ℓ + 30) (t2 := 30 * ℓ + 36) (rdN_spec b h6 _ _ rest hin1 ℓ
        (hvk _ (by simp [intNats])) hℓ) (fun d1 ⟨e1, e2, e3, e4⟩ => ?_)).mono (by unfold unitC; omega)
        (fun _ h => h)
      have d1r : d1.ram sHd = ovw old ((dl.take k).flatMap intNats) := by rw [e2.ram sHd (by simp), h3]
      have d1c : d1.rc sHd = 2 * k := by rw [e2.rc sHd (by simp), h4]
      refine (Hs.seq (t1 := 1) (t2 := 30 * ℓ + 34) (hs_wrM C sHd t3 d1 (by
        rw [d1r, d1c, ovw_length, hWl]; omega)) (fun d2 hd2 => ?_)).mono (by omega) (fun _ h => h)
      subst hd2
      refine (Hs.seq (t1 := 30 * ℓ + 30) (t2 := 3) (rdN_spec _ (cst_put e3 _ _) dl[k].natAbs
        ((dl.drop (k + 1)).flatMap intNats ++ vs) rest (by rw [DS.put_ip]; exact e4) ℓ
        (hvk _ (by simp [intNats])) hℓ) (fun d3 ⟨f1, f2, f3, f4⟩ => ?_)).mono (by omega) (fun _ h => h)
      have d3r : d3.ram sHd = ovw old ((dl.take k).flatMap intNats ++ [if dl[k] < 0 then 1 else 0]) := by
        rw [f2.ram sHd (by simp), DS.put_ram_self, d1r, d1c, ← hWl, putAt_ovw, e1]
      have d3c : d3.rc sHd = 2 * k + 1 := by rw [f2.rc sHd (by simp), DS.put_rc_self, d1c]
      refine (Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C sHd t3 d3 (by
        rw [d3r, d3c, ovw_length]; simp only [List.length_append, List.length_singleton, hWl]; omega))
        (fun d4 hd4 => ?_)).mono (by norm_num) (fun _ h => h)
      subst hd4
      have d4K : (d3.put sHd (d3.env t3)).env gK = k := by
        rw [DS.put_env, f2.fr gK (by decide), DS.put_env, e2.fr gK (by decide), h1]
      refine Hs.mono (hs_inc C gK _ (by rw [d4K]; omega)) le_rfl ?_
      rintro g rfl
      have hsucc : (dl.take (k + 1)).flatMap intNats = (dl.take k).flatMap intNats ++
          [if dl[k] < 0 then 1 else 0] ++ [dl[k].natAbs] := by
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton]
        simp [intNats]
      refine ⟨by vsimp [d4K], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ (show gDn ≠ gK by decide), DS.put_env, f2.fr gDn (by decide), DS.put_env,
          e2.fr gDn (by decide), h2]
      · show (d3.put sHd (d3.env t3)).ram sHd = _
        rw [DS.put_ram_self, d3r, d3c, hsucc, f1]
        have : ((dl.take k).flatMap intNats ++ [if dl[k] < 0 then 1 else 0]).length = 2 * k + 1 := by
          simp [hWl]
        rw [← this, putAt_ovw]
      · show (d3.put sHd (d3.env t3)).rc sHd = _
        rw [DS.put_rc_self, d3c]; omega
      · have r2 : Ran b d1 (natWord (if dl[k] < 0 then 1 else 0)).length [] (gK :: rdNatT) [sHd] :=
          e2.weaken (fun y hy => List.mem_cons_of_mem _ hy) (fun _ h => by simp at h)
        have r4 : Ran (d1.put sHd (d1.env t3)) d3 (natWord dl[k].natAbs).length [] (gK :: rdNatT) [sHd] :=
          f2.weaken (fun y hy => List.mem_cons_of_mem _ hy) (fun _ h => by simp at h)
        have hr := (((h5.trans r2).put (m := sHd) (d1.env t3) (by simp)).trans r4).put (m := sHd) (d3.env t3)
          (by simp)
        have hr2 := hr.set (x := gK) ((d3.put sHd (d3.env t3)).env gK + 1) List.mem_cons_self
        rw [hsucc]
        simp only [List.flatMap_append, List.flatMap_singleton, List.length_append, List.append_nil] at hr2 ⊢
        simpa [Nat.add_assoc] using hr2
      · exact cst_set (cst_put f3 _ _) _ (by decide)
      · simpa using f4)
  refine Hx.hs (Hs.then (hs_rwM C sHd a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C gK _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hN], by simp [ovw_nil, hold'], by simp, ?_,
    cst_set (cst_rew hc _) _ (by decide), by simpa using hin⟩)
    (fun b ⟨_, h2, h3, h4, h5, h6, h7⟩ n hn => ⟨⟨?_, by rw [h4], h2, ?_, h6, ?_⟩, ?_⟩)
  · simpa using ((Ran.refl a (gK :: rdNatT) [sHd]).rew (m := sHd) (by simp)).set (x := gK) 0 List.mem_cons_self
  · rw [h3, List.take_length]
    exact ovw_of_le _ _ (by rw [intNats_flatMap_length]; exact hold)
  · simpa using h5
  · simpa using h7
  · omega

theorem Ran.eqk {a b : DS VV MM} {k k' : ℕ} {w w' : List Bool} {T : List (Fin VV)} {S : List (Fin MM)}
    (h : Ran a b k w T S) (hk : k = k') (hw : w = w') : Ran a b k' w' T S := hk ▸ hw ▸ h

/-! ## The residues -/

theorem rhoS_spec (a : DS VV MM) (hc : Cst a) (r0 r1 : ℤ) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = ([2] ++ intNats r0 ++ intNats r1 ++ vs).flatMap natWord ++ rest)
    (oI wI : List ℕ) (hI : a.ram sI = ovw oI wI) (hIc : a.rc sI = wI.length) (ℓ : ℕ)
    (hv : ∀ v ∈ [2] ++ intNats r0 ++ intNats r1, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C rhoS a (5 * unitC ℓ)
      (fun b => b.ram sI = ovw oI (wI ++ [a.env gP, r0.natAbs, r1.natAbs]) ∧ b.rc sI = wI.length + 3 ∧
        Ran a b (([2] ++ intNats r0 ++ intNats r1).flatMap natWord).length [] rdNatT [sI] ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hin0 : C.inp.drop a.ip = (2 :: (if r0 < 0 then 1 else 0) :: r0.natAbs :: (if r1 < 0 then 1 else 0) ::
      r1.natAbs :: vs).flatMap natWord ++ rest := by rw [hin]; simp [intNats]
  have v2 := hv 2 (by simp)
  have v3 := hv (if r0 < 0 then 1 else 0) (by simp [intNats])
  have v4 := hv r0.natAbs (by simp [intNats])
  have v5 := hv (if r1 < 0 then 1 else 0) (by simp [intNats])
  have v6 := hv r1.natAbs (by simp [intNats])
  have hS : ∀ m ∈ ([] : List (Fin MM)), m ∈ [sI] := fun _ h => by simp at h
  have hT : ∀ y ∈ rdNatT, y ∈ rdNatT := fun _ h => h
  refine Hx.hs (Hs.then (hs_wrM C sI gP a (by rw [hI, hIc, ovw_length]; omega)) (fun b1 hb1 n1 hn1 => ?_))
  subst hb1
  refine Hs.then (rdN_spec _ (cst_put hc _ _) 2 ((if r0 < 0 then 1 else 0) :: r0.natAbs ::
    (if r1 < 0 then 1 else 0) :: r1.natAbs :: vs) rest (by rw [DS.put_ip]; exact hin0) ℓ v2 hℓ)
    (fun b2 ⟨_, e2, e3, e4⟩ n2 hn2 => ?_)
  refine Hs.then (rdN_spec _ e3 _ (r0.natAbs :: (if r1 < 0 then 1 else 0) :: r1.natAbs :: vs) rest e4 ℓ v3 hℓ)
    (fun b3 ⟨_, f2, f3, f4⟩ n3 hn3 => ?_)
  refine Hs.then (rdN_spec _ f3 _ ((if r1 < 0 then 1 else 0) :: r1.natAbs :: vs) rest f4 ℓ v4 hℓ)
    (fun b4 ⟨g1, g2, g3, g4⟩ n4 hn4 => ?_)
  have b4r : b4.ram sI = ovw oI (wI ++ [a.env gP]) := by
    rw [g2.ram sI (by simp), f2.ram sI (by simp), e2.ram sI (by simp), DS.put_ram_self, hI, hIc, putAt_ovw]
  have b4c : b4.rc sI = wI.length + 1 := by
    rw [g2.rc sI (by simp), f2.rc sI (by simp), e2.rc sI (by simp), DS.put_rc_self, hIc]
  refine Hs.then (hs_wrM C sI t3 b4 (by rw [b4r, b4c, ovw_length]; simp)) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  refine Hs.then (rdN_spec _ (cst_put g3 _ _) _ (r1.natAbs :: vs) rest (by rw [DS.put_ip]; exact g4) ℓ v5 hℓ)
    (fun b6 ⟨_, h2, h3, h4⟩ n6 hn6 => ?_)
  refine Hs.then (rdN_spec _ h3 _ vs rest h4 ℓ v6 hℓ) (fun b7 ⟨i1, i2, i3, i4⟩ n7 hn7 => ?_)
  have b7r : b7.ram sI = ovw oI (wI ++ [a.env gP, r0.natAbs]) := by
    rw [i2.ram sI (by simp), h2.ram sI (by simp), DS.put_ram_self, b4r, b4c, g1]
    have : (wI ++ [a.env gP]).length = wI.length + 1 := by simp
    rw [← this, putAt_ovw]; simp
  have b7c : b7.rc sI = wI.length + 2 := by
    rw [i2.rc sI (by simp), h2.rc sI (by simp), DS.put_rc_self, b4c]
  refine Hs.last (hs_wrM C sI t3 b7 (by rw [b7r, b7c, ovw_length]; simp)) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  refine ⟨⟨?_, by rw [DS.put_rc_self, b7c], ?_, cst_put i3 _ _, by rw [DS.put_ip]; exact i4⟩, ?_⟩
  · rw [DS.put_ram_self, b7r, b7c, i1]
    have : (wI ++ [a.env gP, r0.natAbs]).length = wI.length + 2 := by simp
    rw [← this, putAt_ovw]; simp
  · have hr := ((((((Ran.refl a rdNatT [sI]).put (m := sI) (a.env gP) (by simp)).trans (e2.weaken hT hS)).trans
      (f2.weaken hT hS)).trans (g2.weaken hT hS)).put (m := sI) (b4.env t3) (by simp)).trans (h2.weaken hT hS)
      |>.trans (i2.weaken hT hS) |>.put (m := sI) (b7.env t3) (by simp)
    exact hr.eqk (by simp only [intNats, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.append_nil, List.cons_append, List.nil_append, List.length_cons]; omega) (by simp)
  · unfold unitC; omega

/-! ## The entries -/

/-- The variables written by `entsS`. -/
def entT : List (Fin VV) := [gN, gZ, gSg, gB, gSum, t0, t1, t2, t3, t4, vJ]

theorem entsS_spec (a : DS VV MM) (hc : Cst a) (ents : List ℤ) (bits : List ℕ) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = ([ents.length] ++ ents.flatMap intNats ++ vs).flatMap natWord ++ rest)
    (hZ : a.ram sZc = bits) (hbl : bits.length = ents.length)
    (oC wC : List ℕ) (hCr : a.ram sC = ovw oC wC) (hCc : a.rc sC = wC.length) (σ : ℕ) (hσ : a.env gSum = σ)
    (ℓ : ℕ) (hv : ∀ v ∈ [ents.length] ++ ents.flatMap intNats, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hs : σ + (cnts ents bits).sum < 2 ^ C.Wd) :
    Hs C entsS a (a.rc sZc + ents.length * (2 * unitC ℓ + 20) + unitC ℓ + 8)
      (fun b => b.ram sC = ovw oC (wC ++ cnts ents bits) ∧ b.rc sC = wC.length + (cnts ents bits).length ∧
        b.env gSum = σ + (cnts ents bits).sum ∧ b.ram sZc = bits ∧ b.rc sZc = bits.length ∧
        Ran a b (([ents.length] ++ ents.flatMap intNats).flatMap natWord).length [] entT [sZc, sC] ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hsub : ∀ z, (cnts (ents.take z) (bits.take z)).sum ≤ (cnts ents bits).sum := by
    intro z
    have : cnts ents bits = cnts (ents.take z) (bits.take z) ++ cnts (ents.drop z) (bits.drop z) := by
      unfold cnts
      rw [← List.filterMap_append, ← List.zip_append (by simp; omega), List.take_append_drop, List.take_append_drop]
    rw [this, List.sum_append]; omega
  let I : ℕ → DS VV MM → Prop := fun z b => b.env gZ = z ∧ b.env gN = ents.length ∧ b.ram sZc = bits ∧
    b.rc sZc = z ∧ b.ram sC = ovw oC (wC ++ cnts (ents.take z) (bits.take z)) ∧
    b.rc sC = wC.length + (cnts (ents.take z) (bits.take z)).length ∧
    b.env gSum = σ + (cnts (ents.take z) (bits.take z)).sum ∧
    Ran a b (([ents.length] ++ (ents.take z).flatMap intNats).flatMap natWord).length [] entT [sZc, sC] ∧ Cst b ∧
    C.inp.drop b.ip = ((ents.drop z).flatMap intNats ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) gZ gN (by decide) entS ents.length (2 * unitC ℓ + 18) I
    (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro z hz b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      have hz' : ents.drop z = ents[z] :: ents.drop (z + 1) := List.drop_eq_getElem_cons hz
      have hin1 : C.inp.drop b.ip = ((if ents[z] < 0 then 1 else 0) ::
          (ents[z].natAbs :: ((ents.drop (z + 1)).flatMap intNats ++ vs))).flatMap natWord ++ rest := by
        rw [h10, hz', List.flatMap_cons]; simp [intNats]
      have hvz : ∀ v ∈ intNats ents[z], natBitLength v ≤ ℓ := fun v hv' =>
        hv v (List.mem_append_right _ (List.mem_flatMap.mpr ⟨ents[z], List.getElem_mem hz, hv'⟩))
      have hzb : z < bits.length := by omega
      refine (Hs.seq (t1 := unitC ℓ) (t2 := 30 * ℓ + 42) (rdX_spec gSg (by decide) b h9 _ _ rest hin1 ℓ
        (hvz _ (by simp [intNats])) hℓ) (fun d1 ⟨e1, _, e2, e3, e4⟩ => ?_)).mono (by unfold unitC; omega)
        (fun _ h => h)
      refine (Hs.seq (t1 := 30 * ℓ + 30) (t2 := 11) (rdN_spec d1 e3 _ _ rest e4 ℓ (hvz _ (by simp [intNats])) hℓ)
        (fun d2 ⟨f1, f2, f3, f4⟩ => ?_)).mono (by omega) (fun _ h => h)
      have d2Z : d2.ram sZc = bits := by rw [f2.ram sZc (by simp), e2.ram sZc (by simp), h3]
      have d2z : d2.rc sZc = z := by rw [f2.rc sZc (by simp), e2.rc sZc (by simp), h4]
      refine (Hs.seq (t1 := 1) (t2 := 9) (hs_rdM C sZc gB d2 (by rw [d2Z, d2z]; exact hzb))
        (fun d3 hd3 => ?_)).mono (by omega) (fun _ h => h)
      subst hd3
      set d3 := (d2.set gB ((d2.ram sZc).getD (d2.rc sZc) 0)).adv sZc with hd3
      have d3B : d3.env gB = bits[z] := by
        rw [hd3, DS.adv_env, DS.set_env_self, d2Z, d2z, List.getD_eq_getElem _ _ hzb]
      have d3Sg : d3.env gSg = if ents[z] < 0 then 1 else 0 := by
        rw [hd3, DS.adv_env, DS.set_env_ne _ _ (show gSg ≠ gB by decide), f2.fr gSg (by decide), e1]
      have d3t : d3.env t3 = ents[z].natAbs := by
        rw [hd3, DS.adv_env, DS.set_env_ne _ _ (show t3 ≠ gB by decide), f1]
      have d3S : d3.env gSum = σ + (cnts (ents.take z) (bits.take z)).sum := by
        rw [hd3, DS.adv_env, DS.set_env_ne _ _ (show gSum ≠ gB by decide), f2.fr gSum (by decide),
          e2.fr gSum (by decide), h7]
      have d3Cr : d3.ram sC = ovw oC (wC ++ cnts (ents.take z) (bits.take z)) := by
        rw [hd3, DS.adv_ram, DS.set_ram, f2.ram sC (by simp), e2.ram sC (by simp), h5]
      have d3Cc : d3.rc sC = wC.length + (cnts (ents.take z) (bits.take z)).length := by
        rw [hd3, DS.adv_rc_ne _ (by decide), DS.set_rc, f2.rc sC (by simp), e2.rc sC (by simp), h6]
      have d3c : Cst d3 := cst_adv (cst_set f3 _ (by decide)) _
      have hct := cnts_take_succ ents bits z hz hzb
      -- the branch
      let Q : DS VV MM → Prop := fun g => g.env gZ = z ∧ g.env gN = ents.length ∧ g.ram sZc = bits ∧
        g.rc sZc = z + 1 ∧ g.ram sC = ovw oC (wC ++ cnts (ents.take (z + 1)) (bits.take (z + 1))) ∧
        g.rc sC = wC.length + (cnts (ents.take (z + 1)) (bits.take (z + 1))).length ∧
        g.env gSum = σ + (cnts (ents.take (z + 1)) (bits.take (z + 1))).sum ∧
        Ran a g (([ents.length] ++ (ents.take (z + 1)).flatMap intNats).flatMap natWord).length [] entT [sZc, sC] ∧
        Cst g ∧ C.inp.drop g.ip = ((ents.drop (z + 1)).flatMap intNats ++ vs).flatMap natWord ++ rest
      have hR3 : Ran a d3 (([ents.length] ++ (ents.take (z + 1)).flatMap intNats).flatMap natWord).length [] entT
          [sZc, sC] := by
        have r := ((h8.trans (e2.weaken (fun y hy => by revert y; decide) (fun _ h => by simp at h))).trans
          (f2.weaken (fun y hy => by revert y; decide) (fun _ h => by simp at h))).set (x := gB)
          ((d2.ram sZc).getD (d2.rc sZc) 0) (by decide) |>.adv (m := sZc) (by simp)
        refine r.eqk ?_ (by simp)
        simp only [List.take_succ_eq_append_getElem hz, List.flatMap_append, List.flatMap_singleton, intNats,
          List.flatMap_cons, List.flatMap_nil, List.length_append, List.append_nil]
        omega
      have d3Z : d3.env gZ = z := by
        rw [hd3, DS.adv_env, DS.set_env_ne _ _ (show gZ ≠ gB by decide), f2.fr gZ (by decide),
          e2.fr gZ (by decide), h1]
      have d3N : d3.env gN = ents.length := by
        rw [hd3, DS.adv_env, DS.set_env_ne _ _ (show gN ≠ gB by decide), f2.fr gN (by decide),
          e2.fr gN (by decide), h2]
      have d3Zr : d3.ram sZc = bits := by rw [hd3, DS.adv_ram, DS.set_ram, d2Z]
      have d3Zc : d3.rc sZc = z + 1 := by rw [hd3, DS.adv_rc_self, DS.set_rc, d2z]
      have d3i : C.inp.drop d3.ip = ((ents.drop (z + 1)).flatMap intNats ++ vs).flatMap natWord ++ rest := by
        rw [hd3, DS.adv_ip, DS.set_ip]; simpa using f4
      have hbr : Hs C (.ite (.eq gB v1) (.seq (.ite (.eq gSg v1) (.op (.zero t3)) skipS) (.seq (.op (.wrM sC t3))
          (.op (.add gSum t3)))) skipS) d3 7 Q := by
        refine Hs.ite (c := .eq gB v1) (show gB ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
        · have hb1 : bits[z] = 1 := by simpa [Cnd.eval, d3B, d3c.one] using he
          rw [hb1, if_pos rfl] at hct
          have hinner : Hs C (.ite (.eq gSg v1) (.op (.zero t3)) skipS) d3 2
              (fun g => g.env t3 = ents[z].toNat ∧ Ran d3 g 0 [] [t3, vJ] [] ∧ Cst g) := by
            refine Hs.ite (c := .eq gSg v1) (show gSg ≠ v1 by decide) (fun he2 => ?_) (fun he2 => ?_)
            · have hs1 : ents[z] < 0 := by
                have := he2; simp only [Cnd.eval, d3Sg, d3c.one, decide_eq_true_eq] at this
                by_contra h; rw [if_neg h] at this; exact absurd this (by norm_num)
              refine Hs.mono (hs_zero C t3 d3) (by norm_num) ?_
              rintro g rfl
              exact ⟨by rw [DS.set_env_self]; omega, (Ran.refl d3 _ []).set 0 (by decide),
                cst_set d3c _ (by decide)⟩
            · have hs1 : ¬ ents[z] < 0 := by
                intro h; simp [Cnd.eval, d3Sg, d3c.one, h] at he2
              refine Hs.mono (skip_spec d3) (by norm_num) ?_
              rintro g rfl
              exact ⟨by rw [DS.set_env_ne _ _ (show t3 ≠ vJ by decide), d3t]; omega,
                (Ran.refl d3 _ []).set 0 (by decide), cst_set d3c _ (by decide)⟩
          refine (Hs.seq (t1 := 2) (t2 := 3) hinner (fun g1 ⟨k1, k2, k3⟩ => ?_)).mono (by norm_num) (fun _ h => h)
          have g1Cr : g1.ram sC = ovw oC (wC ++ cnts (ents.take z) (bits.take z)) := by
            rw [k2.ram sC (by simp), d3Cr]
          have g1Cc : g1.rc sC = wC.length + (cnts (ents.take z) (bits.take z)).length := by
            rw [k2.rc sC (by simp), d3Cc]
          refine Hs.seq (t1 := 1) (t2 := 1) (hs_wrM C sC t3 g1 (by
            rw [g1Cr, g1Cc, ovw_length]; simp)) (fun g2 hg2 => ?_)
          subst hg2
          have g2S : (g1.put sC (g1.env t3)).env gSum = σ + (cnts (ents.take z) (bits.take z)).sum := by
            rw [DS.put_env, k2.fr gSum (by decide), d3S]
          refine Hs.mono (hs_add C gSum t3 _ (by decide) (by
            rw [g2S, DS.put_env, k1]
            have := hsub (z + 1); rw [hct, List.sum_append, List.sum_singleton] at this; omega)) le_rfl ?_
          rintro g3 rfl
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [DS.set_env_ne _ _ (show gZ ≠ gSum by decide), DS.put_env, k2.fr gZ (by decide), d3Z]
          · rw [DS.set_env_ne _ _ (show gN ≠ gSum by decide), DS.put_env, k2.fr gN (by decide), d3N]
          · rw [DS.set_ram, DS.put_ram_ne _ _ (by decide), k2.ram sZc (by simp), d3Zr]
          · rw [DS.set_rc, DS.put_rc_ne _ _ (by decide), k2.rc sZc (by simp), d3Zc]
          · rw [DS.set_ram, DS.put_ram_self, g1Cr, g1Cc, hct, k1, ← List.append_assoc]
            have : (wC ++ cnts (ents.take z) (bits.take z)).length =
                wC.length + (cnts (ents.take z) (bits.take z)).length := by simp
            rw [← this, putAt_ovw]
          · rw [DS.set_rc, DS.put_rc_self, g1Cc, hct]; simp; omega
          · rw [DS.set_env_self, g2S, DS.put_env, k1, hct, List.sum_append, List.sum_singleton]; ring
          · exact (((hR3.trans (k2.weaken (fun y hy => by revert y; decide) (fun _ h => by simp at h))).put
              (m := sC) (g1.env t3) (by simp)).set (x := gSum) _ (by decide)).eqk (by simp) (by simp)
          · exact cst_set (cst_put k3 _ _) _ (by decide)
          · rw [DS.set_ip, DS.put_ip, k2.ip, Nat.add_zero]; exact d3i
        · have hb1 : bits[z] ≠ 1 := by intro h; simp [Cnd.eval, d3B, d3c.one, h] at he
          rw [if_neg hb1, List.append_nil] at hct
          refine Hs.mono (skip_spec d3) (by norm_num) ?_
          rintro g rfl
          refine ⟨by rw [DS.set_env_ne _ _ (show gZ ≠ vJ by decide), d3Z],
            by rw [DS.set_env_ne _ _ (show gN ≠ vJ by decide), d3N], by rw [DS.set_ram, d3Zr],
            by rw [DS.set_rc, d3Zc], by rw [DS.set_ram, d3Cr, hct], by rw [DS.set_rc, d3Cc, hct],
            by rw [DS.set_env_ne _ _ (show gSum ≠ vJ by decide), d3S, hct], hR3.set _ (by decide),
            cst_set d3c _ (by decide), by rw [DS.set_ip]; exact d3i⟩
      refine (Hs.seq (t1 := 7) (t2 := 1) hbr (fun g ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ => ?_)).mono
        (by norm_num) (fun _ h => h)
      refine Hs.mono (hs_inc C gZ g (by
        rw [q1]; have := lt_two_pow_of_bits (hv ents.length (by simp)) hℓ
        have := lt_natBitLength ents.length; omega)) le_rfl ?_
      rintro g' rfl
      exact ⟨by rw [DS.set_env_self, q1], by rw [DS.set_env_ne _ _ (show gN ≠ gZ by decide), q2], q3, q4, q5,
        q6, by rw [DS.set_env_ne _ _ (show gSum ≠ gZ by decide), q7], q8.set _ (by decide),
        cst_set q9 _ (by decide), by rw [DS.set_ip]; exact q10⟩)
  have hlv := hv ents.length (by simp)
  refine Hx.hs (Hs.then (rdX_spec gN (by decide) a hc ents.length (ents.flatMap intNats ++ vs) rest
    (by rw [hin]; simp) ℓ hlv hℓ) (fun b0 ⟨e1, _, e2, e3, e4⟩ n0 hn0 => ?_))
  refine Hs.then (hs_rwM C sZc b0) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_zero C gZ _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  have hT : ∀ y ∈ gN :: rdNatT, y ∈ entT := fun y hy => by revert y; decide
  have hS : ∀ m ∈ ([] : List (Fin MM)), m ∈ [sZc, sC] := fun _ h => by simp at h
  refine Hs.last (loop _ ⟨by vsimp [], by rw [DS.set_env_ne _ _ (show gN ≠ gZ by decide), DS.rew_env, e1],
    by rw [DS.set_ram, DS.rew_ram, e2.ram sZc (by simp), hZ], by rw [DS.set_rc, DS.rew_rc_self],
    by simp [cnts, e2.ram sC (by simp), hCr], by simp [cnts, DS.rew_rc_ne _ (show sC ≠ sZc by decide), e2.rc sC (by simp), hCc],
    by simp [cnts, DS.set_env_ne _ _ (show gSum ≠ gZ by decide), e2.fr gSum (by decide), hσ], ?_,
    cst_set (cst_rew e3 _) _ (by decide), by simpa using e4⟩)
    (fun b ⟨_, _, h3, h4, h5, h6, h7, h8, h9, h10⟩ n hn => ⟨⟨?_, ?_, ?_, h3, ?_, ?_, h9, ?_⟩, ?_⟩)
  · exact ((((e2.weaken hT hS).rew (m := sZc) (by simp)).set (x := gZ) 0 (by decide))).eqk (by simp) (by simp)
  · rw [h5, List.take_length, ← hbl, List.take_length]
  · rw [h6, List.take_length, ← hbl, List.take_length]
  · rw [h7, List.take_length, ← hbl, List.take_length]
  · rw [h4, hbl]
  · rw [List.take_length] at h8; exact h8
  · simpa using h10
  · have : b0.rc sZc = a.rc sZc := e2.rc sZc (by simp)
    rw [this] at hn1
    have e : ents.length * (2 * unitC ℓ + 18 + 2) = ents.length * (2 * unitC ℓ + 20) := by ring
    omega

/-! ## One table -/

/-- The cost of reading one table, with the store cursors `rH` of `sHd` and `rZ` of `sZc` at its start. -/
def tableCost (ℓ : ℕ) (d : TblD) (rH rZ : ℕ) : ℕ :=
  rH + rZ + (d.pat.length + 2 * d.dl.length + 2 * d.ents.length + 12) * (unitC ℓ + 10)

theorem tblNats_append (d : TblD) (vs : List ℕ) : tblNats d ++ vs = d.s :: d.pat.length :: (d.pat ++
    (d.p :: d.dl.length :: (d.dl.flatMap intNats ++ ([2] ++ intNats d.r0 ++ intNats d.r1 ++
      ([d.ents.length] ++ d.ents.flatMap intNats ++ vs))))) := by
  simp [tblNats]

theorem tableS_spec (a : DS VV MM) (hc : Cst a) (d : TblD) (bits vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (tblNats d ++ vs).flatMap natWord ++ rest)
    (hZ : a.ram sZc = bits) (hbl : bits.length = d.ents.length) (hHd : (a.ram sHd).length ≤ 2 * d.dl.length)
    (oI wI : List ℕ) (hI : a.ram sI = ovw oI wI) (hIc : a.rc sI = wI.length)
    (oC wC : List ℕ) (hCr : a.ram sC = ovw oC wC) (hCc : a.rc sC = wC.length) (σ : ℕ) (hσ : a.env gSum = σ)
    (ℓ : ℕ) (hv : ∀ v ∈ tblNats d, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hs : σ + (cnts d.ents bits).sum < 2 ^ C.Wd) (hpat : d.pat.sum + d.pat.length < 2 ^ C.Wd)
    (hdl : d.dl.length < 2 ^ C.Wd) :
    Hs C tableS a (tableCost ℓ d (a.rc sHd) (a.rc sZc))
      (fun b => b.env gS = d.s ∧ b.env gAct = d.pat.sum % 2 ∧ b.env gDn = d.dl.length ∧
        b.env gSum = σ + (cnts d.ents bits).sum ∧ b.ram sHd = d.dl.flatMap intNats ∧ b.rc sHd = 2 * d.dl.length ∧
        b.ram sI = ovw oI (wI ++ [d.p, d.r0.natAbs, d.r1.natAbs]) ∧ b.rc sI = wI.length + 3 ∧
        b.ram sC = ovw oC (wC ++ cnts d.ents bits) ∧ b.rc sC = wC.length + (cnts d.ents bits).length ∧
        b.ram sZc = bits ∧ b.rc sZc = bits.length ∧
        Ran a b ((tblNats d).flatMap natWord).length [] tblT tblM ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  rw [tblNats_append] at hin
  have hvm : ∀ v, v ∈ tblNats d → natBitLength v ≤ ℓ := hv
  have mS : d.s ∈ tblNats d := by simp [tblNats]
  have mPl : d.pat.length ∈ tblNats d := by simp [tblNats]
  have mPat : ∀ v ∈ d.pat, v ∈ tblNats d := fun v h => by simp [tblNats, h]
  have mP : d.p ∈ tblNats d := by simp [tblNats]
  have mDl : d.dl.length ∈ tblNats d := by simp [tblNats]
  have mD : ∀ v ∈ d.dl.flatMap intNats, v ∈ tblNats d := fun v h => by simp only [tblNats, List.mem_append]; tauto
  have mR : ∀ v ∈ [2] ++ intNats d.r0 ++ intNats d.r1, v ∈ tblNats d := fun v h => by
    simp only [tblNats, List.mem_append] at h ⊢; tauto
  have mE : ∀ v ∈ [d.ents.length] ++ d.ents.flatMap intNats, v ∈ tblNats d := fun v h => by
    simp only [tblNats, List.mem_append] at h ⊢; tauto
  have hS0 : ∀ m ∈ ([] : List (Fin MM)), m ∈ tblM := fun _ h => by simp at h
  -- s
  refine Hx.hs (Hs.then (rdX_spec gS (by decide) a hc _ _ rest hin ℓ (hvm _ mS) hℓ)
    (fun b1 ⟨e1, _, r1, c1, i1⟩ n1 hn1 => ?_))
  -- the pattern
  refine Hs.then (rdX_spec gN (by decide) b1 c1 _ _ rest i1 ℓ (hvm _ mPl) hℓ)
    (fun b2 ⟨e2, _, r2, c2, i2⟩ n2 hn2 => ?_)
  refine Hs.then (patS_spec b2 c2 d.pat _ rest i2 e2 ℓ (fun v h => hvm v (mPat v h)) hℓ hpat)
    (fun b3 ⟨e3, _, r3, c3, i3⟩ n3 hn3 => ?_)
  refine Hs.then (hs_dm C gPar v2 gQ gAct b3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [c3.two]; norm_num) (by
      rw [c3.two]
      calc 2 * 2 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega))) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  set b4 := (b3.set gQ (b3.env gPar / b3.env v2)).set gAct (b3.env gPar % b3.env v2) with hb4
  have c4 : Cst b4 := cst_set (cst_set c3 _ (by decide)) _ (by decide)
  have r4 : Ran b3 b4 0 [] [gQ, gAct] [] := ((Ran.refl b3 _ []).set _ (by decide)).set _ (by decide)
  have i4 : C.inp.drop b4.ip = (d.p :: d.dl.length :: (d.dl.flatMap intNats ++ ([2] ++ intNats d.r0 ++
      intNats d.r1 ++ ([d.ents.length] ++ d.ents.flatMap intNats ++ vs)))).flatMap natWord ++ rest := by
    rw [hb4, DS.set_ip, DS.set_ip]; exact i3
  -- the prime and the digits
  refine Hs.then (rdX_spec gP (by decide) b4 c4 _ _ rest i4 ℓ (hvm _ mP) hℓ)
    (fun b5 ⟨e5, _, r5, c5, i5⟩ n5 hn5 => ?_)
  refine Hs.then (rdX_spec gDn (by decide) b5 c5 _ _ rest i5 ℓ (hvm _ mDl) hℓ)
    (fun b6 ⟨e6, _, r6, c6, i6⟩ n6 hn6 => ?_)
  have b6H : b6.ram sHd = a.ram sHd := by
    rw [r6.ram sHd (by simp), r5.ram sHd (by simp), r4.ram sHd (by simp), r3.ram sHd (by simp),
      r2.ram sHd (by simp), r1.ram sHd (by simp)]
  have b6Hc : b6.rc sHd = a.rc sHd := by
    rw [r6.rc sHd (by simp), r5.rc sHd (by simp), r4.rc sHd (by simp), r3.rc sHd (by simp),
      r2.rc sHd (by simp), r1.rc sHd (by simp)]
  refine Hs.then (dS_spec b6 c6 d.dl _ rest i6 e6 (by rw [b6H]; exact hHd) ℓ (fun v h => hvm v (mD v h)) hℓ hdl)
    (fun b7 ⟨e7, e7c, e7n, r7, c7, i7⟩ n7 hn7 => ?_)
  -- the residues
  have hs7 : ∀ m, m ≠ sHd → b7.ram m = a.ram m ∧ b7.rc m = a.rc m := fun m hm => by
    have h7 : m ∉ [sHd] := by simpa using hm
    exact ⟨by rw [r7.ram m h7, r6.ram m (by simp), r5.ram m (by simp), r4.ram m (by simp), r3.ram m (by simp),
      r2.ram m (by simp), r1.ram m (by simp)], by rw [r7.rc m h7, r6.rc m (by simp), r5.rc m (by simp),
      r4.rc m (by simp), r3.rc m (by simp), r2.rc m (by simp), r1.rc m (by simp)]⟩
  have b7P : b7.env gP = d.p := by rw [r7.fr gP (by decide), r6.fr gP (by decide), e5]
  refine Hs.then (rhoS_spec b7 c7 d.r0 d.r1 _ rest i7 oI wI (by rw [(hs7 sI (by decide)).1, hI])
    (by rw [(hs7 sI (by decide)).2, hIc]) ℓ (fun v h => hvm v (mR v h)) hℓ)
    (fun b8 ⟨e8, e8c, r8, c8, i8⟩ n8 hn8 => ?_)
  -- the entries
  have hs8 : ∀ m, m ≠ sI → b8.ram m = b7.ram m ∧ b8.rc m = b7.rc m := fun m hm => by
    have h8 : m ∉ [sI] := by simpa using hm
    exact ⟨r8.ram m h8, r8.rc m h8⟩
  have b8S : b8.env gSum = σ := by
    rw [r8.fr gSum (by decide), r7.fr gSum (by decide), r6.fr gSum (by decide), r5.fr gSum (by decide),
      r4.fr gSum (by decide), r3.fr gSum (by decide), r2.fr gSum (by decide), r1.fr gSum (by decide), hσ]
  refine Hs.last (entsS_spec b8 c8 d.ents bits vs rest i8
    (by rw [(hs8 sZc (by decide)).1, (hs7 sZc (by decide)).1, hZ]) hbl oC wC
    (by rw [(hs8 sC (by decide)).1, (hs7 sC (by decide)).1, hCr])
    (by rw [(hs8 sC (by decide)).2, (hs7 sC (by decide)).2, hCc]) σ b8S ℓ (fun v h => hvm v (mE v h)) hℓ hs)
    (fun b9 ⟨e9, e9c, e9s, e9z, e9zc, r9, c9, i9⟩ n9 hn9 => ⟨⟨?_, ?_, ?_, e9s, ?_, ?_, ?_, ?_, e9, e9c, e9z, e9zc,
      ?_, c9, i9⟩, ?_⟩)
  · rw [r9.fr gS (by decide), r8.fr gS (by decide), r7.fr gS (by decide), r6.fr gS (by decide),
      r5.fr gS (by decide), r4.fr gS (by decide), r3.fr gS (by decide), r2.fr gS (by decide), e1]
  · rw [r9.fr gAct (by decide), r8.fr gAct (by decide), r7.fr gAct (by decide), r6.fr gAct (by decide),
      r5.fr gAct (by decide), hb4, DS.set_env_self, e3, c3.two]
  · rw [r9.fr gDn (by decide), r8.fr gDn (by decide), e7n]
  · rw [r9.ram sHd (by decide), (hs8 sHd (by decide)).1, e7]
  · rw [r9.rc sHd (by decide), (hs8 sHd (by decide)).2, e7c]
  · rw [r9.ram sI (by decide), e8, b7P]
  · rw [r9.rc sI (by decide), e8c]
  · have hT1 : ∀ y ∈ gS :: rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT2 : ∀ y ∈ gN :: rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT3 : ∀ y ∈ gPar :: gK :: rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT4 : ∀ y ∈ [gQ, gAct], y ∈ tblT := fun y hy => by revert y; decide
    have hT5 : ∀ y ∈ gP :: rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT6 : ∀ y ∈ gDn :: rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT7 : ∀ y ∈ gK :: rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT8 : ∀ y ∈ rdNatT, y ∈ tblT := fun y hy => by revert y; decide
    have hT9 : ∀ y ∈ entT, y ∈ tblT := fun y hy => by revert y; decide
    have hr := (r1.weaken hT1 hS0).trans (r2.weaken hT2 hS0) |>.trans (r3.weaken hT3 hS0)
      |>.trans (r4.weaken hT4 hS0) |>.trans (r5.weaken hT5 hS0) |>.trans (r6.weaken hT6 hS0)
      |>.trans (r7.weaken hT7 (fun m h => by simp at h; subst h; decide))
      |>.trans (r8.weaken hT8 (fun m h => by simp at h; subst h; decide))
      |>.trans (r9.weaken hT9 (fun m h => by simp at h; rcases h with h | h <;> subst h <;> decide))
    refine hr.eqk ?_ (by simp)
    simp only [tblNats, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.length_append,
      List.append_nil, List.cons_append, List.nil_append, List.length_cons]
    omega
  · rw [(hs8 sZc (by decide)).2, (hs7 sZc (by decide)).2] at hn9
    rw [b6Hc] at hn7
    unfold tableCost
    have p1 : d.pat.length * (unitC ℓ + 2) ≤ d.pat.length * (unitC ℓ + 10) := Nat.mul_le_mul_left _ (by omega)
    have p2 : d.dl.length * (2 * unitC ℓ + 2) ≤ d.dl.length * (2 * unitC ℓ + 20) := Nat.mul_le_mul_left _ (by omega)
    have e : (d.pat.length + 2 * d.dl.length + 2 * d.ents.length + 12) * (unitC ℓ + 10) =
      d.pat.length * (unitC ℓ + 10) + d.dl.length * (2 * unitC ℓ + 20) + d.ents.length * (2 * unitC ℓ + 20) +
        12 * unitC ℓ + 120 := by ring
    rw [e]
    omega

end NearQuarticWires.Reconstruct.GatherProg
