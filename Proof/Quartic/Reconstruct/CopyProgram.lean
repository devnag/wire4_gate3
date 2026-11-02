import Proof.Quartic.Reconstruct.Emit
import Proof.Quartic.Reconstruct.SystemsSplit

/-!
# Copying self-delimiting numbers in the cell language

`copyNatS d` reads one `natWord` of the input and writes it at depth `d` of marks (`copyNatS_spec`); `copyNatsS d`
does so for a list of numbers whose length is held in a variable (`copyNatsS_spec`); `rowsCopyS d` copies the rows
`listWord rowWord rows` of an exact system, each row `(p, [ρ_1, ρ_2], 𝒩)` being five numbers (`rowsCopyS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)

variable {C : Ctx}

/-- The effect of reading and writing: the input cursor advances by `k` and the output grows by `w`; the stores and
the call buffers are unchanged, and only the variables in `T` change. -/
structure Moved (a b : DS VV MM) (k : ℕ) (w : List Bool) (T : List (Fin VV)) : Prop where
  ip : b.ip = a.ip + k
  out : b.out = a.out ++ w
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

theorem Moved.refl (a : DS VV MM) (T : List (Fin VV)) : Moved a a 0 [] T :=
  ⟨by simp, by simp, rfl, rfl, rfl, rfl, rfl, Fr.refl a T⟩

theorem Moved.trans {a b c : DS VV MM} {k k' : ℕ} {w w' : List Bool} {T : List (Fin VV)} (h1 : Moved a b k w T)
    (h2 : Moved b c k' w' T) : Moved a c (k + k') (w ++ w') T :=
  ⟨by rw [h2.ip, h1.ip, Nat.add_assoc], by rw [h2.out, h1.out, List.append_assoc], h2.ram.trans h1.ram,
    h2.rc.trans h1.rc, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc, Fr.trans h1.fr h2.fr⟩

theorem Moved.set {a b : DS VV MM} {k : ℕ} {w : List Bool} {T : List (Fin VV)} (h : Moved a b k w T) {x : Fin VV}
    (v : ℕ) (hx : x ∈ T) : Moved a (b.set x v) k w T :=
  ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx)⟩

theorem Moved.weaken {a b : DS VV MM} {k : ℕ} {w : List Bool} {T T' : List (Fin VV)} (h : Moved a b k w T)
    (hT : ∀ y ∈ T, y ∈ T') : Moved a b k w T' :=
  ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, h.fr.weaken hT⟩

theorem Moved.of_wrote {a b : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : Wrote a b w T) :
    Moved a b 0 w T := ⟨by rw [h.ip]; simp, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, h.fr⟩

/-- Copy one `natWord` from the input to the output at depth `d`. -/
def copyNatS (d : ℕ) : St VV MM := .seq rdNatI (emitNatD d)

/-- The variables written by `copyNatS`. -/
def copyT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, t5, t6, t7, t8, t9]

/-- The cost of copying a number of bit length `ℓ`. -/
def copyCost (d ℓ : ℕ) : ℕ := 30 * ℓ + 31 + emitNatDCost d ℓ

theorem copyNatS_spec (d : ℕ) (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (copyNatS d) a (copyCost d (natBitLength v))
      (fun b => Moved a b (natWord v).length (marksD d (natWord v)) copyT ∧ Cst b ∧ b.env t3 = v) := by
  have hWd : 2 ≤ C.Wd := by omega
  refine Hs.seq (t1 := 30 * natBitLength v + 30) (t2 := emitNatDCost d (natBitLength v))
    (rdNatI_spec a hc v rest hin hW) (fun b ⟨h1, _, h3, h4, h5⟩ => ?_) |>.mono (by unfold copyCost; omega)
    (fun _ h => h)
  have hb : Cst b := Cst.of_fr hc h5 (by decide)
  have hv : natBitLength (b.env t3) + 2 < 2 ^ C.Wd := by
    rw [h1]
    exact lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) hW)
  refine (emitNatD_spec d b hb hWd hv).mono (by rw [h1]) ?_
  rintro c ⟨wc, cc⟩
  simp only [Prod.mk.injEq] at h4
  obtain ⟨o4, r4, c4, i4, k4, kc4⟩ := h4
  refine ⟨⟨by rw [wc.ip, h3], by rw [wc.out, o4, h1], by rw [wc.ram, r4], by rw [wc.rc, c4], by rw [wc.kin, i4],
    by rw [wc.kout, k4], by rw [wc.kc, kc4], ?_⟩, cc, by rw [wc.fr t3 (by decide), h1]⟩
  exact Fr.trans (h5.weaken (by decide)) (wc.fr.weaken (by decide))

/-! ## A list of numbers -/

/-- The number of numbers to copy. -/
def cN : Fin VV := ⟨57, by decide⟩
/-- The counter of the copied numbers. -/
def cK : Fin VV := ⟨58, by decide⟩

/-- Copy `cN` numbers. -/
def copyNatsS (d : ℕ) : St VV MM := .seq (.op (.zero cK)) (.loop (.lt cK cN) (.seq (copyNatS d) (.op (.inc cK))))

/-- The variables written by `copyNatsS`. -/
def copyNatsT : List (Fin VV) := cK :: copyT

theorem copyNatsS_spec (d ℓ : ℕ) (a : DS VV MM) (hc : Cst a) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = vs.flatMap natWord ++ rest) (hN : a.env cN = vs.length)
    (hW : ∀ v ∈ vs, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hNW : vs.length < 2 ^ C.Wd) :
    Hs C (copyNatsS d) a (vs.length * (copyCost d ℓ + 4) + 4)
      (fun b => Moved a b (vs.flatMap natWord).length (marksD d (vs.flatMap natWord)) copyNatsT ∧ Cst b) := by
  have hct : ∀ y ∈ copyT, y ∈ copyNatsT := fun y hy => List.mem_cons_of_mem _ hy
  have hK : cK ∈ copyNatsT := by decide
  have hcT : vZ ∉ copyNatsT ∧ v1 ∉ copyNatsT ∧ v2 ∉ copyNatsT := by decide
  let I : ℕ → DS VV MM → Prop := fun k b => b.env cK = k ∧ b.env cN = vs.length ∧
    Moved a b ((vs.take k).flatMap natWord).length (marksD d ((vs.take k).flatMap natWord)) copyNatsT ∧ Cst b
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt cK cN) (.seq (copyNatS d) (.op (.inc cK)))) b
      (vs.length * ((copyCost d ℓ + 2) + 2) + 2) (I vs.length) := by
    refine Hs.loopN (c := .lt cK cN) (show cK ≠ cN by decide) I vs.length (copyCost d ℓ + 2) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4⟩
      refine ⟨by simp only [Cnd.eval, h1, h2, decide_eq_true_eq]; exact hk, ?_⟩
      have e1 : vs.flatMap natWord ++ rest = (vs.take k).flatMap natWord ++ ((vs.drop k).flatMap natWord ++ rest) := by
        rw [← List.append_assoc, ← List.flatMap_append, List.take_append_drop]
      have hinb : C.inp.drop b.ip = natWord vs[k] ++ ((vs.drop (k + 1)).flatMap natWord ++ rest) := by
        rw [h3.ip, ← List.drop_drop, hin, e1, List.drop_left, List.drop_eq_getElem_cons hk, List.flatMap_cons,
          List.append_assoc]
      have hvk : natBitLength vs[k] ≤ ℓ := hW _ (List.getElem_mem hk)
      refine Hs.seq (t1 := copyCost d ℓ) (t2 := 1) ((copyNatS_spec d b h4 vs[k] _ hinb (by omega)).mono
        (by unfold copyCost emitNatDCost; have := Nat.mul_le_mul_left (4 * 2 ^ d + 20) (show natBitLength vs[k] + 3 ≤ ℓ + 3 by omega); omega)
        (fun _ h => h)) (fun e ⟨we, ce, _⟩ => ?_)
      have eK : e.env cK = k := by rw [we.fr cK (by decide), h1]
      have eN : e.env cN = vs.length := by rw [we.fr cN (by decide), h2]
      refine Hs.mono (hs_inc C cK e (by rw [eK]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨by vsimp [eK], by vsimp [eN], ?_, ⟨by vsimp [ce.z], by vsimp [ce.one], by vsimp [ce.two]⟩⟩
      have hw := (h3.trans (we.weaken hct)).set (x := cK) (e.env cK + 1) hK
      rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton, marksD_append,
        List.length_append]
      exact hw
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  refine Hx.hs (Hs.then (hs_zero C cK a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hN], by simpa [marksD] using (Moved.refl a copyNatsT).set 0 hK,
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩) (fun b hb n hn => ?_)
  obtain ⟨_, _, h3, h4⟩ := hb
  rw [List.take_length] at h3
  refine ⟨⟨h3, h4⟩, ?_⟩
  have : vs.length * (copyCost d ℓ + 2 + 2) = vs.length * (copyCost d ℓ + 4) := by ring
  omega

/-! ## The rows of a system -/

/-- The five numbers of a row `(p, [ρ_1, ρ_2], 𝒩)`. -/
def rowNats (row : ℕ × List ℕ × ℕ) : List ℕ := [row.1, 2, row.2.1.getD 0 0, row.2.1.getD 1 0, row.2.2]

theorem rowWord_eq (row : ℕ × List ℕ × ℕ) (h : row.2.1.length = 2) : rowWord row = (rowNats row).flatMap natWord := by
  obtain ⟨p, l, c⟩ := row
  match l, h with
  | [x, y], _ => simp [rowWord, rowNats, listWord, List.append_assoc]

theorem rowsWord_eq (rows : List (ℕ × List ℕ × ℕ)) (h : ∀ row ∈ rows, row.2.1.length = 2) :
    listWord rowWord rows = natWord rows.length ++ (rows.flatMap rowNats).flatMap natWord := by
  unfold listWord
  congr 1
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun row hr => rowWord_eq row (h row hr)

theorem rowNats_length (rows : List (ℕ × List ℕ × ℕ)) : (rows.flatMap rowNats).length = 5 * rows.length := by
  induction rows with
  | nil => simp
  | cons r rs ih => rw [List.flatMap_cons, List.length_append, ih]; simp [rowNats]; ring

/-- Copy the rows of an exact system: the number of rows, then five numbers per row. -/
def rowsCopyS (d : ℕ) : St VV MM :=
  .seq (copyNatS d) (.seq (.op (.copy cN t3)) (.seq (.op (.add cN t3)) (.seq (.op (.add cN t3))
    (.seq (.op (.add cN t3)) (.seq (.op (.add cN t3)) (copyNatsS d))))))

/-- The variables written by `rowsCopyS`. -/
def rowsCopyT : List (Fin VV) := cN :: copyNatsT

theorem rowsCopyS_spec (d ℓ : ℕ) (a : DS VV MM) (hc : Cst a) (rows : List (ℕ × List ℕ × ℕ)) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord rowWord rows ++ rest) (h2 : ∀ row ∈ rows, row.2.1.length = 2)
    (hW : ∀ v ∈ rows.length :: rows.flatMap rowNats, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hNW : 5 * rows.length < 2 ^ C.Wd) :
    Hs C (rowsCopyS d) a ((5 * rows.length + 1) * (copyCost d ℓ + 4) + 20)
      (fun b => Moved a b (listWord rowWord rows).length (marksD d (listWord rowWord rows)) rowsCopyT ∧
        Cst b) := by
  have hcr : ∀ y ∈ copyT, y ∈ rowsCopyT := fun y hy => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)
  have hnr : ∀ y ∈ copyNatsT, y ∈ rowsCopyT := fun y hy => List.mem_cons_of_mem _ hy
  have hN : cN ∈ rowsCopyT := by decide
  have heq := rowsWord_eq rows h2
  rw [heq] at hin
  have hl0 : natBitLength rows.length ≤ ℓ := hW _ (by simp)
  have hW' : ∀ v ∈ rows.flatMap rowNats, natBitLength v ≤ ℓ := fun v hv => hW v (List.mem_cons_of_mem _ hv)
  refine Hx.hs (Hs.then (copyNatS_spec d a hc rows.length _ (by rw [hin, List.append_assoc]) (by omega))
    (fun b0 ⟨w0, c0, t0e⟩ n0 hn0 => ?_))
  refine Hs.then (hs_copy C cN t3 b0 (by decide)) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_add C cN t3 _ (by decide) (by vsimp [t0e]; omega)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  refine Hs.then (hs_add C cN t3 _ (by decide) (by vsimp [t0e]; omega)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_add C cN t3 _ (by decide) (by vsimp [t0e]; omega)) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (hs_add C cN t3 _ (by decide) (by vsimp [t0e]; omega)) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  set b5 := ((((b0.set cN (b0.env t3)).set cN ((b0.set cN (b0.env t3)).env cN + (b0.set cN (b0.env t3)).env t3)).set
    cN _).set cN _).set cN _ with hb5def
  have c5 : Cst b5 := ⟨by vsimp [hb5def, c0.z], by vsimp [hb5def, c0.one], by vsimp [hb5def, c0.two]⟩
  have e5 : b5.env cN = (rows.flatMap rowNats).length := by rw [rowNats_length]; vsimp [hb5def, t0e]; ring
  have m5 : Moved a b5 (natWord rows.length).length (marksD d (natWord rows.length)) rowsCopyT :=
    (((((w0.weaken hcr).set _ hN).set _ hN).set _ hN).set _ hN).set _ hN
  have hin5 : C.inp.drop b5.ip = (rows.flatMap rowNats).flatMap natWord ++ rest := by
    rw [m5.ip, ← List.drop_drop, hin, List.append_assoc, List.drop_left]
  refine Hs.last (copyNatsS_spec d ℓ b5 c5 _ rest hin5 e5 hW' hℓ (by rw [rowNats_length]; exact hNW))
    (fun b6 ⟨w6, c6⟩ n6 hn6 => ?_)
  refine ⟨⟨?_, c6⟩, ?_⟩
  · have hm := m5.trans (w6.weaken hnr)
    rw [heq, marksD_append, List.length_append]
    exact hm
  · rw [rowNats_length] at hn6
    have k : copyCost d (natBitLength rows.length) ≤ copyCost d ℓ := by
      unfold copyCost emitNatDCost
      have := Nat.mul_le_mul_left (4 * 2 ^ d + 20) (show natBitLength rows.length + 3 ≤ ℓ + 3 by omega)
      omega
    nlinarith

end NearQuarticWires.Reconstruct
