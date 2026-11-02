import Proof.Quartic.Reconstruct.TotalProg

/-!
# The sum of the answers: the whole run

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`itemsS` runs `itemS` on every answered system (`itemsS_spec`); `totalS` reads `n` and the number of systems, runs
`itemsS` and writes `intWord (P − N)` (`totalS_run`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.Reconstruct.TotalProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.Reconstruct NearQuarticWires.Reconstruct.GatherProg

variable {C : Ctx}

/-- **A loop counted by `x < y`** with a cost per pass. -/
theorem loopCntc (x y : Fin VV) (hxy : x ≠ y) (body : St VV MM) (N : ℕ) (t : ℕ → ℕ) (I : ℕ → DS VV MM → Prop)
    (hI : ∀ k b, I k b → b.env x = k ∧ b.env y = N)
    (hstep : ∀ k < N, ∀ b, I k b → Hs C body b (t k) (I (k + 1))) :
    ∀ a, I 0 a → Hs C (.loop (.lt x y) body) a ((∑ k ∈ Finset.range N, (t k + 2)) + 2) (I N) := by
  refine Hs.loopNc (c := .lt x y) hxy I N t (fun k hk b hb => ⟨?_, hstep k hk b hb⟩) (fun b hb => ?_)
  · obtain ⟨h1, h2⟩ := hI k b hb
    simp only [Cnd.eval, h1, h2, decide_eq_true_eq]; exact hk
  · obtain ⟨h1, h2⟩ := hI N b hb
    simp [Cnd.eval, h1, h2]

/-- The empty answered system. -/
def d0 : ItD := ⟨0, 0, 0, none⟩

/-- Run `itemS` on every answered system. -/
def itemsS : St VV MM := .seq (.op (.zero tI)) (.loop (.lt tI tM) itemS)

theorem itemsS_spec (a : DS VV MM) (hc : Cst a) (its : List ItD) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (its.flatMap itN ++ vs).flatMap natWord ++ rest) (hM : a.env tM = its.length)
    (hP : a.env tP = 0) (hN : a.env tN = 0) (ℓ : ℕ) (hv : ∀ d ∈ its, ∀ v ∈ itN d, natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd)
    (hW : (its.map posOf).sum + (its.map negOf).sum + (its.map prodOf).sum + its.length + 1 < 2 ^ C.Wd) :
    Hs C itemsS a ((∑ k ∈ Finset.range its.length, (itCost ℓ (its.getD k d0) + 2)) + 4)
      (fun b => b.env tP = (its.map posOf).sum ∧ b.env tN = (its.map negOf).sum ∧
        Ran a b ((its.flatMap itN).flatMap natWord).length [] itT [] ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hsub : ∀ (f : ItD → ℕ) k, ((its.take k).map f).sum ≤ (its.map f).sum := fun f k =>
    List.Sublist.sum_le_sum ((List.take_sublist k its).map f) (fun _ _ => Nat.zero_le _)
  let I : ℕ → DS VV MM → Prop := fun i b => b.env tI = i ∧ b.env tM = its.length ∧
    b.env tP = ((its.take i).map posOf).sum ∧ b.env tN = ((its.take i).map negOf).sum ∧
    Ran a b (((its.take i).flatMap itN).flatMap natWord).length [] itT [] ∧ Cst b ∧
    C.inp.drop b.ip = ((its.drop i).flatMap itN ++ vs).flatMap natWord ++ rest
  have loop := loopCntc (C := C) tI tM (by decide) itemS its.length (fun k => itCost ℓ (its.getD k d0)) I
    (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro i hi b ⟨h1, h2, h3, h4, h5, h6, h7⟩
      have hmem : its[i] ∈ its := List.getElem_mem hi
      have hd : its.drop i = its[i] :: its.drop (i + 1) := List.drop_eq_getElem_cons hi
      have hin1 : C.inp.drop b.ip = (itN its[i] ++ ((its.drop (i + 1)).flatMap itN ++ vs)).flatMap natWord ++ rest := by
        rw [h7, hd, List.flatMap_cons, List.append_assoc]
      have hpr : prodOf its[i] ≤ (its.map prodOf).sum := List.le_sum_of_mem (List.mem_map_of_mem hmem)
      have hp1 := hsub posOf i
      have hn1 := hsub negOf i
      have hg : its.getD i d0 = its[i] := List.getD_eq_getElem _ _ hi
      rw [hg]
      refine (itemS_spec b h6 its[i] _ rest hin1 _ _ i h3 h4 h1 ℓ (hv _ hmem) hℓ (by omega)).mono le_rfl ?_
      rintro d ⟨e1, e2, e3, r, cd, id⟩
      refine ⟨e3, by rw [r.fr tM (by decide), h2], ?_, ?_, ?_, cd, id⟩
      · rw [e1, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]; simp
      · rw [e2, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]; simp
      · refine (h5.trans r).eqk ?_ rfl
        rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.flatMap_singleton, List.flatMap_append,
          List.length_append])
  refine Hx.hs (Hs.then (hs_zero C tI a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hM], by vsimp [hP], by vsimp [hN],
    ((Ran.refl a itT []).set 0 (by decide)).eqk (by simp) rfl, cst_set hc _ (by decide), by simpa using hin⟩)
    (fun b ⟨_, _, h3, h4, h5, h6, h7⟩ n hn => ⟨⟨by rw [h3, List.take_length], by rw [h4, List.take_length],
      by rw [List.take_length] at h5; exact h5, h6, by simpa using h7⟩, by omega⟩)

/-! ## The whole program -/

/-- **The sum of the answers.** -/
def totalS : St VV MM := .seq NearCubicGates.Close.CounterMachine.PrefixProg.cstInit (.seq rdNatI (.seq (rdTo tM)
  (.seq (.op (.zero tP)) (.seq (.op (.zero tN)) (.seq itemsS (emitShiftD 0 tP tN))))))

/-- The cost of the whole run. -/
def totalCost (ℓ : ℕ) (its : List ItD) : ℕ :=
  (∑ k ∈ Finset.range its.length, (itCost ℓ (its.getD k d0) + 2)) + 2 * unitC ℓ + emitShiftCost 0 ℓ + 30

theorem totalS_run (C : Ctx) (n : ℕ) (its : List ItD) (ℓ : ℕ)
    (hinp : C.inp = (n :: its.length :: its.flatMap itN).flatMap natWord) (hℓ : ℓ + 2 ≤ C.Wd)
    (hn : natBitLength n ≤ ℓ) (hm : natBitLength its.length ≤ ℓ) (hv : ∀ d ∈ its, ∀ v ∈ itN d, natBitLength v ≤ ℓ)
    (hW : (its.map posOf).sum + (its.map negOf).sum + (its.map prodOf).sum + its.length + 1 < 2 ^ C.Wd)
    (hPN : natBitLength ((its.map posOf).sum + (its.map negOf).sum) ≤ ℓ) :
    Hs C totalS (a0 : DS VV MM) (totalCost ℓ its)
      (fun b => b.out = NearCubicGates.Close.Interfaces.intWord
        (((its.map posOf).sum : ℤ) - ((its.map negOf).sum : ℤ))) := by
  refine Hx.hs (Hs.then (NearCubicGates.Close.CounterMachine.PrefixProg.cstInit_spec C (by omega))
    (fun d ⟨cd, _, _, dip, dout, _, _, _⟩ n0 hn0 => ?_))
  have hin : C.inp.drop d.ip = (n :: (its.length :: (its.flatMap itN ++ []))).flatMap natWord ++ [] := by
    rw [dip, List.drop_zero, hinp]; simp
  refine Hs.then (rdN_spec d cd n _ [] hin ℓ hn hℓ) (fun b1 ⟨_, r1, c1, i1⟩ n1 hn1 => ?_)
  refine Hs.then (rdX_spec tM (by decide) b1 c1 its.length _ [] i1 ℓ hm hℓ) (fun b2 ⟨e2, _, r2, c2, i2⟩ n2 hn2 => ?_)
  refine Hs.then (hs_zero C tP b2) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_zero C tN _) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (itemsS_spec _ (cst_set (cst_set c2 _ (by decide)) _ (by decide)) its [] [] (by simpa using i2)
    (by vsimp [e2]) (by vsimp []) (by vsimp []) ℓ hv hℓ hW) (fun b5 ⟨e5, f5, r5, c5, _⟩ n5 hn5 => ?_)
  have hWd : natBitLength (b5.env tP + b5.env tN) + 2 < 2 ^ C.Wd := by
    rw [e5, f5]
    exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hs.last (emitShiftD_spec 0 tP tN (by decide) (by decide) (by decide) b5 c5 (by omega) hWd)
    (fun b6 ⟨w6, _⟩ n6 hn6 => ⟨?_, ?_⟩)
  · rw [w6.out, r5.out]
    simp only [DS.set_out]
    rw [r2.out, r1.out, dout, e5, f5, marksD_zero]
    simp
  · have hc : emitShiftCost 0 (natBitLength (b5.env tP + b5.env tN)) ≤ emitShiftCost 0 ℓ := by
      unfold emitShiftCost emitNatDCost; rw [e5, f5]; nlinarith
    unfold totalCost unitC at *
    omega

end NearQuarticWires.Reconstruct.TotalProg
