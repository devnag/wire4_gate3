import Proof.Quartic.Reconstruct.GatherProgTable
import Proof.Gates.CounterMachine.PrefixRun
import Proof.Quartic.Reconstruct.EmitInt

/-!
# The sum of the answers: the program

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The word after `solved` is `natWord n` and, for every listed system, its tag (the coefficient `(±1)κ_σ` and the
position of the point `0`) and the solver's answer, all numbers (`ItD`, `itN`). `totalS` reads them and sums the
products of the coefficient and the numerator of the value at the point `0`, the products of equal signs into
`tP` and the others into `tN` (`itemS_spec`, `itemsS_spec`), and writes `intWord (P − N)` (`totalS_run`).
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

/-! ## Variables -/

/-- The number of systems. -/
def tM : Fin VV := ⟨90, by decide⟩
/-- The sum of the products of equal signs. -/
def tP : Fin VV := ⟨91, by decide⟩
/-- The sum of the products of opposite signs. -/
def tN : Fin VV := ⟨92, by decide⟩
/-- The system counter. -/
def tI : Fin VV := ⟨93, by decide⟩
/-- The sign of the coefficient. -/
def tCs : Fin VV := ⟨94, by decide⟩
/-- The magnitude of the coefficient. -/
def tCa : Fin VV := ⟨95, by decide⟩
/-- The position of the point `0`. -/
def tIdx : Fin VV := ⟨96, by decide⟩
/-- The flag of the answer. -/
def tF : Fin VV := ⟨97, by decide⟩
/-- The sign of the numerator kept. -/
def tVs : Fin VV := ⟨98, by decide⟩
/-- The magnitude of the numerator kept. -/
def tVa : Fin VV := ⟨99, by decide⟩
/-- A product. -/
def tPr : Fin VV := ⟨100, by decide⟩
/-- The length of the answer. -/
def tL : Fin VV := ⟨101, by decide⟩
/-- The entry counter. -/
def tK : Fin VV := ⟨102, by decide⟩
/-- The sign of a numerator. -/
def tNs : Fin VV := ⟨103, by decide⟩
/-- The magnitude of a numerator. -/
def tNa : Fin VV := ⟨104, by decide⟩

/-! ## The data -/

/-- One answered system as the program reads it: the sign and magnitude of the coefficient, the position of the
point `0`, and the answer (for each value: the sign and magnitude of the numerator and the denominator). -/
structure ItD where
  cs : ℕ
  ca : ℕ
  idx : ℕ
  ans : Option (List (ℕ × ℕ × ℕ))

/-- The numbers of one value. -/
def entN (e : ℕ × ℕ × ℕ) : List ℕ := [e.1, e.2.1, e.2.2]

/-- The numbers of an answer. -/
def ansN : Option (List (ℕ × ℕ × ℕ)) → List ℕ
  | none => [0]
  | some L => [1, L.length] ++ L.flatMap entN

/-- The numbers of one answered system. -/
def itN (d : ItD) : List ℕ := [d.cs, d.ca, d.idx] ++ ansN d.ans

/-- The value kept: the sign and magnitude of the numerator at the position of the point `0`. -/
def valOf (d : ItD) : ℕ × ℕ :=
  match d.ans with
  | none => (0, 0)
  | some L => if d.idx < L.length then ((L.getD d.idx (0, 0, 0)).1, (L.getD d.idx (0, 0, 0)).2.1) else (0, 0)

/-- The product of the magnitudes. -/
def prodOf (d : ItD) : ℕ := d.ca * (valOf d).2

/-- The product when the signs agree. -/
def posOf (d : ItD) : ℕ := if d.cs = (valOf d).1 then prodOf d else 0

/-- The product when the signs differ. -/
def negOf (d : ItD) : ℕ := if d.cs = (valOf d).1 then 0 else prodOf d

/-- The number of values of an answer. -/
def ansLen (d : ItD) : ℕ :=
  match d.ans with
  | none => 0
  | some L => L.length

/-! ## The program -/

/-- One value of an answer: keep it if it is at the position of the point `0`. -/
def entS : St VV MM := .seq (rdTo tNs) (.seq (rdTo tNa) (.seq rdNatI (.seq (.ite (.eq tK tIdx)
  (.seq (.op (.copy tVs tNs)) (.op (.copy tVa tNa))) skipS) (.op (.inc tK)))))

/-- The values of an answer. -/
def ansS : St VV MM := .seq (rdTo tL) (.seq (.op (.zero tK)) (.loop (.lt tK tL) entS))

/-- One answered system. -/
def itemS : St VV MM := .seq (rdTo tCs) (.seq (rdTo tCa) (.seq (rdTo tIdx) (.seq (rdTo tF) (.seq (.op (.zero tVs))
  (.seq (.op (.zero tVa)) (.seq (.ite (.eq tF v1) ansS skipS) (.seq (.op (.mul tCa tVa tPr))
    (.seq (.ite (.eq tCs tVs) (.op (.add tP tPr)) (.op (.add tN tPr))) (.op (.inc tI))))))))))

/-- The variables written by `itemS`. -/
def itT : List (Fin VV) := [tCs, tCa, tIdx, tF, tVs, tVa, tPr, tL, tK, tNs, tNa, tP, tN, tI, t0, t1, t2, t3, t4, vJ]

/-! ## The values of an answer -/

/-- The variables written by `ansS`. -/
def ansT : List (Fin VV) := [tL, tK, tNs, tNa, tVs, tVa, t0, t1, t2, t3, t4, vJ]

/-- The value kept after the first `k` values. -/
def selK (L : List (ℕ × ℕ × ℕ)) (idx k : ℕ) : ℕ × ℕ :=
  if idx < k then ((L.getD idx (0, 0, 0)).1, (L.getD idx (0, 0, 0)).2.1) else (0, 0)

theorem ansS_spec (a : DS VV MM) (hc : Cst a) (L : List (ℕ × ℕ × ℕ)) (idx : ℕ) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (L.length :: (L.flatMap entN ++ vs)).flatMap natWord ++ rest) (hI : a.env tIdx = idx)
    (hVs : a.env tVs = 0) (hVa : a.env tVa = 0) (ℓ : ℕ) (hv : ∀ v ∈ L.length :: L.flatMap entN, natBitLength v ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C ansS a (unitC ℓ + L.length * (3 * unitC ℓ + 14) + 5)
      (fun b => b.env tVs = (selK L idx L.length).1 ∧ b.env tVa = (selK L idx L.length).2 ∧
        Ran a b ((L.length :: L.flatMap entN).flatMap natWord).length [] ansT [] ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hL := hv L.length List.mem_cons_self
  have hvL : ∀ v ∈ L.flatMap entN, natBitLength v ≤ ℓ := fun v h => hv v (List.mem_cons_of_mem _ h)
  refine Hx.hs (Hs.then (rdX_spec tL (by decide) a hc L.length _ rest hin ℓ hL hℓ)
    (fun b1 ⟨e1, _, r1, c1, i1⟩ n1 hn1 => ?_))
  refine Hs.then (hs_zero C tK b1) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  let I : ℕ → DS VV MM → Prop := fun k b => b.env tK = k ∧ b.env tL = L.length ∧ b.env tIdx = idx ∧
    b.env tVs = (selK L idx k).1 ∧ b.env tVa = (selK L idx k).2 ∧
    Ran a b ((L.length :: (L.take k).flatMap entN).flatMap natWord).length [] ansT [] ∧ Cst b ∧
    C.inp.drop b.ip = ((L.drop k).flatMap entN ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) tK tL (by decide) entS L.length (3 * unitC ℓ + 12) I (fun k b hb => ⟨hb.1, hb.2.1⟩)
    (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      have hd : L.drop k = L[k] :: L.drop (k + 1) := List.drop_eq_getElem_cons hk
      have hin1 : C.inp.drop b.ip = (L[k].1 :: L[k].2.1 :: L[k].2.2 :: ((L.drop (k + 1)).flatMap entN ++ vs)).flatMap
          natWord ++ rest := by
        rw [h8, hd, List.flatMap_cons]
        simp only [entN, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_append, List.append_assoc]
      have hvk : ∀ v ∈ entN L[k], natBitLength v ≤ ℓ := fun v h => hvL v (List.mem_flatMap.mpr ⟨L[k],
        List.getElem_mem hk, h⟩)
      refine (Hs.seq (t1 := unitC ℓ) (t2 := 2 * unitC ℓ + 10) (rdX_spec tNs (by decide) b h7 _ _ rest hin1 ℓ
        (hvk _ (by simp [entN])) hℓ) (fun d1 ⟨f1, _, s1, c1', i1'⟩ => ?_)).mono (by omega) (fun _ h => h)
      refine (Hs.seq (t1 := unitC ℓ) (t2 := unitC ℓ + 9) (rdX_spec tNa (by decide) d1 c1' _ _ rest i1' ℓ
        (hvk _ (by simp [entN])) hℓ) (fun d2 ⟨f2, _, s2, c2, i2⟩ => ?_)).mono (by omega) (fun _ h => h)
      refine (Hs.seq (t1 := 30 * ℓ + 30) (t2 := 6) (rdN_spec d2 c2 _ _ rest i2 ℓ (hvk _ (by simp [entN])) hℓ)
        (fun d3 ⟨_, s3, c3, i3⟩ => ?_)).mono (by unfold unitC; omega) (fun _ h => h)
      have d3K : d3.env tK = k := by
        rw [s3.fr tK (by decide), s2.fr tK (by decide), s1.fr tK (by decide), h1]
      have d3I : d3.env tIdx = idx := by
        rw [s3.fr tIdx (by decide), s2.fr tIdx (by decide), s1.fr tIdx (by decide), h3]
      have d3Ns : d3.env tNs = L[k].1 := by rw [s3.fr tNs (by decide), s2.fr tNs (by decide), f1]
      have d3Na : d3.env tNa = L[k].2.1 := by rw [s3.fr tNa (by decide), f2]
      have d3Vs : d3.env tVs = (selK L idx k).1 := by
        rw [s3.fr tVs (by decide), s2.fr tVs (by decide), s1.fr tVs (by decide), h4]
      have d3Va : d3.env tVa = (selK L idx k).2 := by
        rw [s3.fr tVa (by decide), s2.fr tVa (by decide), s1.fr tVa (by decide), h5]
      have hr3 : Ran a d3 ((L.length :: (L.take (k + 1)).flatMap entN).flatMap natWord).length [] ansT [] := by
        have w : ∀ y ∈ tNs :: rdNatT, y ∈ ansT := fun y hy => by revert y; decide
        have w2 : ∀ y ∈ tNa :: rdNatT, y ∈ ansT := fun y hy => by revert y; decide
        have w3 : ∀ y ∈ rdNatT, y ∈ ansT := fun y hy => by revert y; decide
        refine (((h6.trans (s1.weaken w (fun _ h => h))).trans (s2.weaken w2 (fun _ h => h))).trans
          (s3.weaken w3 (fun _ h => h))).eqk ?_ (by simp)
        rw [List.take_succ_eq_append_getElem hk]
        simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_singleton, entN, List.flatMap_nil,
          List.length_append, List.append_nil]
        omega
      let Q : DS VV MM → Prop := fun g => g.env tK = k ∧ g.env tL = L.length ∧ g.env tIdx = idx ∧
        g.env tVs = (selK L idx (k + 1)).1 ∧ g.env tVa = (selK L idx (k + 1)).2 ∧
        Ran a g ((L.length :: (L.take (k + 1)).flatMap entN).flatMap natWord).length [] ansT [] ∧ Cst g ∧
        C.inp.drop g.ip = ((L.drop (k + 1)).flatMap entN ++ vs).flatMap natWord ++ rest
      have d3L : d3.env tL = L.length := by
        rw [s3.fr tL (by decide), s2.fr tL (by decide), s1.fr tL (by decide), h2]
      have hbr : Hs C (.ite (.eq tK tIdx) (.seq (.op (.copy tVs tNs)) (.op (.copy tVa tNa))) skipS) d3 4 Q := by
        refine Hs.ite (c := .eq tK tIdx) (show tK ≠ tIdx by decide) (fun he => ?_) (fun he => ?_)
        · have hki : k = idx := by simpa [Cnd.eval, d3K, d3I] using he
          refine (Hs.seq (t1 := 1) (t2 := 1) (hs_copy C tVs tNs d3 (by decide)) (fun g1 hg1 => ?_)).mono
            (by norm_num) (fun _ h => h)
          subst hg1
          refine Hs.mono (hs_copy C tVa tNa _ (by decide)) le_rfl ?_
          rintro g2 rfl
          have hsel : selK L idx (k + 1) = (L[k].1, L[k].2.1) := by
            unfold selK; rw [if_pos (by omega), ← hki, List.getD_eq_getElem _ _ hk]
          refine ⟨by vsimp [d3K], by vsimp [d3L], by vsimp [d3I], by vsimp [hsel, d3Ns], by vsimp [hsel, d3Na],
            ((hr3.set _ (by decide)).set _ (by decide)), cst_set (cst_set c3 _ (by decide)) _ (by decide),
            by simpa using i3⟩
        · have hki : k ≠ idx := by simpa [Cnd.eval, d3K, d3I] using he
          have hsel : selK L idx (k + 1) = selK L idx k := by
            unfold selK
            by_cases h : idx < k
            · rw [if_pos (by omega), if_pos h]
            · rw [if_neg (by omega), if_neg h]
          refine (skip_spec d3).mono (by norm_num) ?_
          rintro g rfl
          refine ⟨by vsimp [d3K], by vsimp [d3L], by vsimp [d3I], by vsimp [hsel, d3Vs], by vsimp [hsel, d3Va],
            hr3.set _ (by decide), cst_set c3 _ (by decide), by simpa using i3⟩
      refine (Hs.seq (t1 := 4) (t2 := 1) hbr (fun g ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ => ?_)).mono (by norm_num)
        (fun _ h => h)
      refine Hs.mono (hs_inc C tK g (by rw [q1]; have := lt_two_pow_of_bits hL hℓ; omega)) le_rfl ?_
      rintro g' rfl
      exact ⟨by vsimp [q1], by vsimp [q2], by vsimp [q3], by vsimp [q4], by vsimp [q5], q6.set _ (by decide),
        cst_set q7 _ (by decide), by simpa using q8⟩)
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [e1], by vsimp [r1.fr tIdx (by decide), hI],
    by vsimp [r1.fr tVs (by decide), hVs, selK], by vsimp [r1.fr tVa (by decide), hVa, selK],
    ((r1.weaken (fun y hy => by revert y; decide) (fun _ h => h)).set _ (by decide)).eqk (by simp) rfl,
    cst_set c1 _ (by decide), by simpa using i1⟩)
    (fun b ⟨_, _, _, h4, h5, h6, h7, h8⟩ n hn => ⟨⟨h4, h5, by rw [List.take_length] at h6; exact h6, h7,
      by simpa using h8⟩, ?_⟩)
  have e : L.length * (3 * unitC ℓ + 12 + 2) = L.length * (3 * unitC ℓ + 14) := by ring
  omega

/-! ## One answered system -/

/-- The cost of one answered system. -/
def itCost (ℓ : ℕ) (d : ItD) : ℕ := 5 * unitC ℓ + ansLen d * (3 * unitC ℓ + 14) + 30

theorem itemS_spec (a : DS VV MM) (hc : Cst a) (d : ItD) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (itN d ++ vs).flatMap natWord ++ rest) (P N i : ℕ) (hP : a.env tP = P) (hN : a.env tN = N)
    (hI : a.env tI = i) (ℓ : ℕ) (hv : ∀ v ∈ itN d, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hW : P + N + prodOf d + i + 1 < 2 ^ C.Wd) :
    Hs C itemS a (itCost ℓ d)
      (fun b => b.env tP = P + posOf d ∧ b.env tN = N + negOf d ∧ b.env tI = i + 1 ∧
        Ran a b ((itN d).flatMap natWord).length [] itT [] ∧ Cst b ∧ C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  have hin0 : C.inp.drop a.ip = (d.cs :: d.ca :: d.idx :: (ansN d.ans ++ vs)).flatMap natWord ++ rest := by
    rw [hin]; simp [itN]
  have m1 : d.cs ∈ itN d := by simp [itN]
  have m2 : d.ca ∈ itN d := by simp [itN]
  have m3 : d.idx ∈ itN d := by simp [itN]
  have mA : ∀ v ∈ ansN d.ans, v ∈ itN d := fun v h => by simp [itN, h]
  refine Hx.hs (Hs.then (rdX_spec tCs (by decide) a hc _ _ rest hin0 ℓ (hv _ m1) hℓ)
    (fun b1 ⟨e1, _, r1, c1, i1⟩ n1 hn1 => ?_))
  refine Hs.then (rdX_spec tCa (by decide) b1 c1 _ _ rest i1 ℓ (hv _ m2) hℓ) (fun b2 ⟨e2, _, r2, c2, i2⟩ n2 hn2 => ?_)
  refine Hs.then (rdX_spec tIdx (by decide) b2 c2 _ _ rest i2 ℓ (hv _ m3) hℓ) (fun b3 ⟨e3, _, r3, c3, i3⟩ n3 hn3 => ?_)
  -- the flag
  have hflag : ∃ f rest', ansN d.ans = f :: rest' ∧ (f = 1 ↔ d.ans.isSome) := by
    cases d.ans with
    | none => exact ⟨0, [], rfl, by simp⟩
    | some L => exact ⟨1, L.length :: L.flatMap entN, rfl, by simp⟩
  obtain ⟨f, rest', hf, hf1⟩ := hflag
  have i3' : C.inp.drop b3.ip = (f :: (rest' ++ vs)).flatMap natWord ++ rest := by rw [i3, hf]; rfl
  refine Hs.then (rdX_spec tF (by decide) b3 c3 _ _ rest i3' ℓ (hv _ (mA _ (by rw [hf]; exact List.mem_cons_self))) hℓ)
    (fun b4 ⟨e4, _, r4, c4, i4⟩ n4 hn4 => ?_)
  have w : ∀ x : Fin VV, x ∈ itT → ∀ y ∈ x :: rdNatT, y ∈ itT := fun x hx y hy => by
    rcases List.mem_cons.mp hy with h | h
    · rw [h]; exact hx
    · exact (by decide : ∀ y ∈ rdNatT, y ∈ itT) y h
  have r4' : Ran a b4 ((d.cs :: d.ca :: d.idx :: [f]).flatMap natWord).length [] itT [] :=
    ((((r1.weaken (w tCs (by decide)) (fun _ h => h)).trans (r2.weaken (w tCa (by decide)) (fun _ h => h))).trans
      (r3.weaken (w tIdx (by decide)) (fun _ h => h))).trans (r4.weaken (w tF (by decide)) (fun _ h => h))).eqk
      (by simp; omega) (by simp)
  have b4f : ∀ x, x ∉ itT → b4.env x = a.env x := fun x hx => r4'.fr x hx
  have b4Cs : b4.env tCs = d.cs := by rw [r4.fr tCs (by decide), r3.fr tCs (by decide), r2.fr tCs (by decide), e1]
  have b4Ca : b4.env tCa = d.ca := by rw [r4.fr tCa (by decide), r3.fr tCa (by decide), e2]
  have b4Idx : b4.env tIdx = d.idx := by rw [r4.fr tIdx (by decide), e3]
  have b4P : b4.env tP = P := by
    rw [r4.fr tP (by decide), r3.fr tP (by decide), r2.fr tP (by decide), r1.fr tP (by decide), hP]
  have b4N : b4.env tN = N := by
    rw [r4.fr tN (by decide), r3.fr tN (by decide), r2.fr tN (by decide), r1.fr tN (by decide), hN]
  have b4I : b4.env tI = i := by
    rw [r4.fr tI (by decide), r3.fr tI (by decide), r2.fr tI (by decide), r1.fr tI (by decide), hI]
  refine Hs.then (hs_zero C tVs b4) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  refine Hs.then (hs_zero C tVa _) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  have c6 : Cst ((b4.set tVs 0).set tVa 0) := cst_set (cst_set c4 _ (by decide)) _ (by decide)
  have hr6 : Ran a ((b4.set tVs 0).set tVa 0) ((d.cs :: d.ca :: d.idx :: [f]).flatMap natWord).length [] itT [] :=
    (r4'.set _ (by decide)).set _ (by decide)
  have s6 : ∀ x, x ≠ tVs → x ≠ tVa → ((b4.set tVs 0).set tVa 0).env x = b4.env x := fun x h1 h2 => by
    rw [DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
  have i6 : C.inp.drop ((b4.set tVs 0).set tVa 0).ip = (rest' ++ vs).flatMap natWord ++ rest := by
    simpa using i4
  -- the answer
  let Q : DS VV MM → Prop := fun g => g.env tVs = (valOf d).1 ∧ g.env tVa = (valOf d).2 ∧ g.env tCs = d.cs ∧
    g.env tCa = d.ca ∧ g.env tP = P ∧ g.env tN = N ∧ g.env tI = i ∧
    Ran a g ((itN d).flatMap natWord).length [] itT [] ∧ Cst g ∧ C.inp.drop g.ip = vs.flatMap natWord ++ rest
  have hans : Hs C (.ite (.eq tF v1) ansS skipS) ((b4.set tVs 0).set tVa 0)
      (unitC ℓ + ansLen d * (3 * unitC ℓ + 14) + 6) Q := by
    refine Hs.ite (c := .eq tF v1) (show tF ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hf1' : f = 1 := by
        have : ((b4.set tVs 0).set tVa 0).env tF = 1 := by simpa [Cnd.eval, c6.one] using he
        rwa [s6 tF (by decide) (by decide), e4] at this
      obtain ⟨L, hL⟩ : ∃ L, d.ans = some L := Option.isSome_iff_exists.mp (hf1.mp hf1')
      have hA : ansN d.ans = 1 :: (L.length :: L.flatMap entN) := by rw [hL]; rfl
      have hrest : rest' = L.length :: L.flatMap entN := by rw [hf] at hA; exact (List.cons.inj hA).2
      have hvL : ∀ v ∈ L.length :: L.flatMap entN, natBitLength v ≤ ℓ := fun v h =>
        hv v (mA v (by rw [hA]; exact List.mem_cons_of_mem _ h))
      refine (ansS_spec _ c6 L d.idx vs rest (by rw [i6, hrest]; simp) (by rw [s6 tIdx (by decide) (by decide), b4Idx])
        (by vsimp []) (by vsimp []) ℓ hvL hℓ).mono (by simp only [ansLen, hL]; omega) ?_
      rintro g ⟨g1, g2, r, cg, ig⟩
      have hval : valOf d = selK L d.idx L.length := by unfold valOf selK; rw [hL]
      have fr : ∀ x, x ∉ ansT → x ≠ tVs → x ≠ tVa → g.env x = b4.env x := fun x hx h1 h2 => by
        rw [r.fr x hx, s6 x h1 h2]
      refine ⟨by rw [g1, hval], by rw [g2, hval], by rw [fr tCs (by decide) (by decide) (by decide), b4Cs],
        by rw [fr tCa (by decide) (by decide) (by decide), b4Ca], by rw [fr tP (by decide) (by decide) (by decide), b4P],
        by rw [fr tN (by decide) (by decide) (by decide), b4N], by rw [fr tI (by decide) (by decide) (by decide), b4I],
        ?_, cg, ig⟩
      refine (hr6.trans (r.weaken (fun y hy => by revert y; decide) (fun _ h => h))).eqk ?_ (by simp)
      simp only [itN, hA, hf1', List.flatMap_cons, List.flatMap_append, List.length_append, List.flatMap_nil,
        List.cons_append, List.nil_append, List.append_nil]
      omega
    · have hf1' : f ≠ 1 := by
        intro h
        have : ((b4.set tVs 0).set tVa 0).env tF = 1 := by rw [s6 tF (by decide) (by decide), e4, h]
        simp [Cnd.eval, c6.one, this] at he
      have hnone : d.ans = none := by
        cases h : d.ans with
        | none => rfl
        | some L => exact absurd (hf1.mpr (by rw [h]; rfl)) hf1'
      have hA : ansN d.ans = [0] := by rw [hnone]; rfl
      have hrest : rest' = [] := by rw [hf] at hA; exact (List.cons.inj hA).2
      have hf0 : f = 0 := by rw [hf] at hA; exact (List.cons.inj hA).1
      have hval : valOf d = (0, 0) := by unfold valOf; rw [hnone]
      refine (skip_spec _).mono (by omega) ?_
      rintro g rfl
      refine ⟨by rw [hval, DS.set_env_ne _ _ (show tVs ≠ vJ by decide)]; vsimp [],
        by rw [hval, DS.set_env_ne _ _ (show tVa ≠ vJ by decide)]; vsimp [],
        by rw [DS.set_env_ne _ _ (show tCs ≠ vJ by decide), s6 tCs (by decide) (by decide), b4Cs],
        by rw [DS.set_env_ne _ _ (show tCa ≠ vJ by decide), s6 tCa (by decide) (by decide), b4Ca],
        by rw [DS.set_env_ne _ _ (show tP ≠ vJ by decide), s6 tP (by decide) (by decide), b4P],
        by rw [DS.set_env_ne _ _ (show tN ≠ vJ by decide), s6 tN (by decide) (by decide), b4N],
        by rw [DS.set_env_ne _ _ (show tI ≠ vJ by decide), s6 tI (by decide) (by decide), b4I], ?_,
        cst_set c6 _ (by decide), by rw [DS.set_ip]; simpa [hrest] using i6⟩
      refine (hr6.set _ (by decide)).eqk ?_ rfl
      simp only [itN, hA, hf0, List.flatMap_cons, List.flatMap_append, List.length_append, List.flatMap_nil,
        List.cons_append, List.nil_append, List.append_nil]
  refine Hs.then hans (fun g ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ n7 hn7 => ?_)
  refine Hs.then (hs_mul C tCa tVa tPr g (by decide) (by decide) (by decide) (by
    rw [q4, q2]; unfold prodOf at hW; omega)) (fun g1 hg1 n8 hn8 => ?_)
  subst hg1
  have g1Pr : (g.set tPr (g.env tCa * g.env tVa)).env tPr = prodOf d := by rw [DS.set_env_self, q4, q2]; rfl
  have g1f : ∀ x, x ≠ tPr → (g.set tPr (g.env tCa * g.env tVa)).env x = g.env x := fun x hx => DS.set_env_ne _ _ hx
  let R : DS VV MM → Prop := fun h => h.env tP = P + posOf d ∧ h.env tN = N + negOf d ∧ h.env tI = i ∧
    Ran a h ((itN d).flatMap natWord).length [] itT [] ∧ Cst h ∧ C.inp.drop h.ip = vs.flatMap natWord ++ rest
  have hadd : Hs C (.ite (.eq tCs tVs) (.op (.add tP tPr)) (.op (.add tN tPr))) (g.set tPr (g.env tCa * g.env tVa))
      2 R := by
    have rg : Ran a (g.set tPr (g.env tCa * g.env tVa)) ((itN d).flatMap natWord).length [] itT [] :=
      q8.set _ (by decide)
    have cg : Cst (g.set tPr (g.env tCa * g.env tVa)) := cst_set q9 _ (by decide)
    refine Hs.ite (c := .eq tCs tVs) (show tCs ≠ tVs by decide) (fun he => ?_) (fun he => ?_)
    · have hs : d.cs = (valOf d).1 := by
        have := he; simp only [Cnd.eval, decide_eq_true_eq, g1f tCs (by decide), g1f tVs (by decide), q3, q1] at this
        exact this
      refine Hs.mono (hs_add C tP tPr _ (by decide) (by
        rw [g1Pr, g1f tP (by decide), q5]; omega)) le_rfl ?_
      rintro h rfl
      refine ⟨by rw [DS.set_env_self, g1Pr, g1f tP (by decide), q5, posOf, if_pos hs],
        by rw [DS.set_env_ne _ _ (show tN ≠ tP by decide), g1f tN (by decide), q6, negOf, if_pos hs, Nat.add_zero],
        by rw [DS.set_env_ne _ _ (show tI ≠ tP by decide), g1f tI (by decide), q7], rg.set _ (by decide),
        cst_set cg _ (by decide), by rw [DS.set_ip, DS.set_ip]; exact q10⟩
    · have hs : d.cs ≠ (valOf d).1 := by
        have := he; simp only [Cnd.eval, decide_eq_false_iff_not, g1f tCs (by decide), g1f tVs (by decide), q3, q1]
          at this
        exact this
      refine Hs.mono (hs_add C tN tPr _ (by decide) (by
        rw [g1Pr, g1f tN (by decide), q6]; omega)) le_rfl ?_
      rintro h rfl
      refine ⟨by rw [DS.set_env_ne _ _ (show tP ≠ tN by decide), g1f tP (by decide), q5, posOf, if_neg hs,
          Nat.add_zero],
        by rw [DS.set_env_self, g1Pr, g1f tN (by decide), q6, negOf, if_neg hs],
        by rw [DS.set_env_ne _ _ (show tI ≠ tN by decide), g1f tI (by decide), q7], rg.set _ (by decide),
        cst_set cg _ (by decide), by rw [DS.set_ip, DS.set_ip]; exact q10⟩
  refine Hs.then hadd (fun h ⟨k1, k2, k3, k4, k5, k6⟩ n9 hn9 => ?_)
  refine Hs.last (hs_inc C tI h (by rw [k3]; omega)) (fun h' hh' n10 hn10 => ?_)
  subst hh'
  refine ⟨⟨by rw [DS.set_env_ne _ _ (show tP ≠ tI by decide), k1], by rw [DS.set_env_ne _ _ (show tN ≠ tI by decide), k2],
    by rw [DS.set_env_self, k3], k4.set _ (by decide), cst_set k5 _ (by decide), by rw [DS.set_ip]; exact k6⟩, ?_⟩
  unfold itCost
  omega

end NearQuarticWires.Reconstruct.TotalProg
