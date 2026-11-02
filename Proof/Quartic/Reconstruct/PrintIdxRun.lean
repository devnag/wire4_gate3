import Proof.Quartic.Reconstruct.PrintIdx

/-!
# The run of the index writer

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`printIdxS_spec`: from the counters and the constants held in variables, `printIdxS` writes `printIdxW …` at depth `2`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

theorem iV_step (x : Fin VV) (hx : x ∉ printIdxT) {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w printIdxT)
    (hc : Cst b) (v : ℕ) (hv : b.env x = v) (hW : 2 ≤ C.Wd) (hbits : natBitLength v + 2 < 2 ^ C.Wd) :
    Hs C (emitV x 2) b (emitNatDCost 2 (natBitLength v) + 2)
      (fun c => OutMoved a c (w ++ marksD 2 (natWord v)) printIdxT ∧ Cst c) := by
  have hxt : x ≠ t3 := fun h => hx (by rw [h]; decide)
  refine (emitV_spec x hxt 2 b hc acc.rcok hW (by rw [hv]; exact hbits)).mono (by rw [hv]) ?_
  intro c ⟨m, cc⟩
  rw [hv] at m
  exact ⟨acc.trans (m.weaken (by decide)), cc⟩

theorem iC_step (y : Fin VV) (hy : y ∉ printIdxT) {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w printIdxT)
    (hc : Cst b) :
    Hs C (.op (.copy qPw y)) b 1 (fun c => OutMoved a c (w ++ []) printIdxT ∧ Cst c ∧ c.env qPw = b.env y) := by
  have hyp : qPw ≠ y := fun h => hy (by rw [← h]; decide)
  refine Hs.mono (hs_copy C qPw y b hyp) le_rfl ?_
  rintro c rfl
  exact ⟨acc.trans ⟨by simp, rfl, rfl, rfl, rfl, rfl, Fr.set b _ (by decide), fun m => by simp; exact acc.rcok m⟩,
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩, DS.set_env_self _ _ _⟩

theorem iS_step (x : Fin VV) (hx : x ∉ printIdxT) (hx0 : x ≠ vZ) {a b : DS VV MM} {w : List Bool}
    (acc : OutMoved a b w printIdxT) (hc : Cst b) (v : ℕ) (hv : b.env x = v) (hW : 2 ≤ C.Wd)
    (hbits : natBitLength v + 2 < 2 ^ C.Wd) :
    Hs C (emitShiftD 2 x vZ) b (emitShiftCost 2 (natBitLength v))
      (fun c => OutMoved a c (w ++ marksD 2 (NearCubicGates.Close.Interfaces.intWord ((v : ℤ) - (0 : ℕ)))) printIdxT ∧
        Cst c) := by
  have hxs : x ∉ emitShiftT := fun h => hx (List.mem_append_right _ h)
  refine (emitShift_rc x vZ hx0 hxs (by decide) b hc acc.rcok hW (by rw [hv, hc.z, Nat.add_zero]; exact hbits)).mono
    (by rw [hv, hc.z, Nat.add_zero]) ?_
  intro c ⟨m, _, cc⟩
  rw [hv, hc.z] at m
  exact ⟨acc.trans (m.weaken (fun y hy => List.mem_append_right _ hy)), cc⟩

theorem iSig_step {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w printIdxT) (hc : Cst b) (is : ℕ)
    (hsig : b.env qSig = is) (h8 : b.env q8 = 8) (hpw : b.env qPw = 128) (h512 : 512 ≤ 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C (digLoopS qSig v2 q8 (emitV qDg 2)) b (8 * (emitNatDCost 2 1 + 2 + 4 + 4 + 4) + 4)
      (fun c => OutMoved a c (w ++ (List.range 8).flatMap (fun j => marksD 2 (natWord ((is / 2 ^ (8 - 1 - j)) % 2))))
        printIdxT ∧ Cst c) := by
  refine (digLoopS_spec qSig v2 q8 (emitV qDg 2) (fun v => marksD 2 (natWord v)) emitVT (emitNatDCost 2 1 + 2)
    (by decide) (by decide) (by decide) is 2 8 (by norm_num) b (fun c cc cok hd _ => ?_) hc acc.rcok hsig hc.two h8
    (by rw [hpw]; norm_num) (by omega) (by omega)).mono le_rfl (fun c ⟨m, cc⟩ => ⟨acc.trans m, cc⟩)
  have hb1 : natBitLength (c.env qDg) ≤ 1 := natBitLength_le_of_lt_two_pow (by omega) le_rfl
  refine (emitV_rc qDg (by decide) 2 c cc cok hW (by omega)).mono ?_ (fun d h => h)
  have := emitNatDCost_mono 2 hb1
  omega

theorem iDig_step (X O : Fin VV) (hXO : X ∉ printIdxT ∧ O ∉ printIdxT ∧ O ≠ qDg ∧ X ≠ qBase ∧ X ≠ qJp1)
    {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w printIdxT) (hc : Cst b) (x B J1 o : ℕ) (hB : 0 < B)
    (hx : b.env X = x) (hb : b.env qBase = B) (hj : b.env qJp1 = J1) (hpw : b.env qPw = B ^ (J1 - 1))
    (ho : b.env O = o) (hBW : 2 * B ^ J1 ≤ 2 ^ C.Wd) (hJW : J1 < 2 ^ C.Wd) (ℓ : ℕ) (hℓ : natBitLength (B + o) ≤ ℓ)
    (hW : ℓ + 3 ≤ C.Wd) :
    Hs C (digLoopS X qBase qJp1 (emitShiftD 2 qDg O)) b (J1 * (emitShiftCost 2 ℓ + 4 + 4 + 4) + 4)
      (fun c => OutMoved a c (w ++ (List.range J1).flatMap (fun j => marksD 2 (NearCubicGates.Close.Interfaces.intWord
        ((((x / B ^ (J1 - 1 - j)) % B : ℕ) : ℤ) - (o : ℤ))))) printIdxT ∧ Cst c) := by
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hXd : X ∉ digT ∧ X ∉ emitVT := ⟨fun h => hXO.1 (List.mem_append_left _ h),
    fun h => hXO.1 (List.mem_append_right _ h)⟩
  have hOs : O ∉ emitShiftT := fun h => hXO.2.1 (List.mem_append_right _ h)
  have hOT : O ∉ digT ++ emitVT := hXO.2.1
  refine (digLoopS_spec X qBase qJp1 (emitShiftD 2 qDg O)
    (fun v => marksD 2 (NearCubicGates.Close.Interfaces.intWord ((v : ℤ) - (o : ℤ)))) emitVT (emitShiftCost 2 ℓ)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact hXd
        · decide
        · decide) (by decide) (by decide) x B J1 hB b (fun c cc cok hd hfr => ?_) hc acc.rcok hx hb hj hpw hBW
    hJW).mono le_rfl (fun c ⟨m, cc⟩ => ⟨acc.trans m, cc⟩)
  have hcO : c.env O = o := by rw [hfr O hOT, ho]
  have hbits : natBitLength (c.env qDg + c.env O) ≤ ℓ := (natBitLength_mono (by rw [hcO]; omega)).trans hℓ
  refine (emitShift_rc qDg O (Ne.symm hXO.2.2.1) (by decide) hOs c cc cok (by omega) (by omega)).mono
    (emitShiftCost_mono 2 hbits) (fun d ⟨m, r, cd⟩ => ⟨?_, r, cd⟩)
  rw [hcO] at m
  exact m

/-- The cost of `printIdxS`. -/
def printIdxCost (ℓ J1 : ℕ) : ℕ :=
  5 * (emitNatDCost 2 ℓ + 2) + (8 * (emitNatDCost 2 1 + 2 + 4 + 4 + 4) + 4) +
    2 * (J1 * (emitShiftCost 2 ℓ + 4 + 4 + 4) + 4) + 2 * emitShiftCost 2 ℓ + 20

/-- **Writing the index of a table.** -/
theorem printIdxS_spec (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length)
    (sb is p len B J1 x0 x1 o0 o1 y0 y1 : ℕ) (h1 : a.env qSb = sb) (h2 : a.env q8 = 8) (h3 : a.env q128 = 128)
    (h4 : a.env qSig = is) (h5 : a.env qP = p) (h6 : a.env qLen = len) (h7 : a.env qTop = B ^ (J1 - 1))
    (h8 : a.env qBase = B) (h9 : a.env qJp1 = J1) (h10 : a.env qX0 = x0) (h11 : a.env qX1 = x1) (h12 : a.env qO0 = o0)
    (h13 : a.env qO1 = o1) (h14 : a.env qR0 = y0) (h15 : a.env qR1 = y1) (hB : 0 < B) (ℓ : ℕ)
    (hℓ : ∀ v ∈ [sb, 8, p, len, 2, B + o0, B + o1, y0, y1], natBitLength v ≤ ℓ) (hW : ℓ + 3 ≤ C.Wd)
    (hBW : 2 * B ^ J1 ≤ 2 ^ C.Wd) (hJW : J1 < 2 ^ C.Wd) (h512 : 512 ≤ 2 ^ C.Wd) :
    Hs C printIdxS a (printIdxCost ℓ J1)
      (fun c => OutMoved a c (printIdxW sb is p len B J1 x0 x1 o0 o1 y0 y1) printIdxT ∧ Cst c) := by
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have bw : ∀ v, v ∈ [sb, 8, p, len, 2, B + o0, B + o1, y0, y1] → natBitLength v + 2 < 2 ^ C.Wd := fun v hv => by
    have := hℓ v hv; omega
  have hc2 : a.env v2 = 2 := hc.two
  have acc0 : OutMoved a a [] printIdxT := OutMoved.refl a printIdxT hok
  unfold printIdxS
  refine Hx.hs (Hs.then (iV_step qSb (by decide) acc0 hc sb (by rw [acc0.fr qSb (by decide), h1]) (by omega) (bw sb (by simp))) (fun b1 ⟨acc1, c1⟩ n1 hn1 => ?_))
  refine Hs.then (iV_step q8 (by decide) acc1 c1 8 (by rw [acc1.fr q8 (by decide), h2]) (by omega) (bw 8 (by simp))) (fun b2 ⟨acc2, c2⟩ n2 hn2 => ?_)
  refine Hs.then (iC_step q128 (by decide) acc2 c2) (fun b3 ⟨acc3, c3, pw3⟩ n3 hn3 => ?_)
  refine Hs.then (iSig_step acc3 c3 is (by rw [acc3.fr qSig (by decide), h4]) (by rw [acc3.fr q8 (by decide), h2]) (by rw [pw3, acc2.fr q128 (by decide), h3]) h512 (by omega)) (fun b4 ⟨acc4, c4⟩ n4 hn4 => ?_)
  refine Hs.then (iV_step qP (by decide) acc4 c4 p (by rw [acc4.fr qP (by decide), h5]) (by omega) (bw p (by simp))) (fun b5 ⟨acc5, c5⟩ n5 hn5 => ?_)
  refine Hs.then (iV_step qLen (by decide) acc5 c5 len (by rw [acc5.fr qLen (by decide), h6]) (by omega) (bw len (by simp))) (fun b6 ⟨acc6, c6⟩ n6 hn6 => ?_)
  refine Hs.then (iC_step qTop (by decide) acc6 c6) (fun b7 ⟨acc7, c7, pw7⟩ n7 hn7 => ?_)
  refine Hs.then (iDig_step qX0 qO0 (by decide) acc7 c7 x0 B J1 o0 hB (by rw [acc7.fr qX0 (by decide), h10]) (by rw [acc7.fr qBase (by decide), h8]) (by rw [acc7.fr qJp1 (by decide), h9]) (by rw [pw7, acc6.fr qTop (by decide), h7]) (by rw [acc7.fr qO0 (by decide), h12]) hBW hJW ℓ (hℓ _ (by simp)) hW) (fun b8 ⟨acc8, c8⟩ n8 hn8 => ?_)
  refine Hs.then (iC_step qTop (by decide) acc8 c8) (fun b9 ⟨acc9, c9, pw9⟩ n9 hn9 => ?_)
  refine Hs.then (iDig_step qX1 qO1 (by decide) acc9 c9 x1 B J1 o1 hB (by rw [acc9.fr qX1 (by decide), h11]) (by rw [acc9.fr qBase (by decide), h8]) (by rw [acc9.fr qJp1 (by decide), h9]) (by rw [pw9, acc8.fr qTop (by decide), h7]) (by rw [acc9.fr qO1 (by decide), h13]) hBW hJW ℓ (hℓ _ (by simp)) hW) (fun b10 ⟨acc10, c10⟩ n10 hn10 => ?_)
  refine Hs.then (iV_step v2 (by decide) acc10 c10 2 (by rw [acc10.fr v2 (by decide), hc2]) (by omega) (bw 2 (by simp))) (fun b11 ⟨acc11, c11⟩ n11 hn11 => ?_)
  refine Hs.then (iS_step qR0 (by decide) (by decide) acc11 c11 y0 (by rw [acc11.fr qR0 (by decide), h14]) (by omega) (bw y0 (by simp))) (fun b12 ⟨acc12, c12⟩ n12 hn12 => ?_)
  refine Hs.last (iS_step qR1 (by decide) (by decide) acc12 c12 y1 (by rw [acc12.fr qR1 (by decide), h15]) (by omega) (bw y1 (by simp))) (fun b13 ⟨acc13, c13⟩ n13 hn13 => ⟨⟨?_, c13⟩, ?_⟩)
  · unfold printIdxW
    simpa [List.append_assoc] using acc13
  · have e : ∀ v ∈ [sb, 8, p, len, 2], emitNatDCost 2 (natBitLength v) ≤ emitNatDCost 2 ℓ :=
      fun v hv => emitNatDCost_mono 2 (hℓ v (by simp at hv ⊢; tauto))
    have s0 : emitShiftCost 2 (natBitLength y0) ≤ emitShiftCost 2 ℓ := emitShiftCost_mono 2 (hℓ y0 (by simp))
    have s1 : emitShiftCost 2 (natBitLength y1) ≤ emitShiftCost 2 ℓ := emitShiftCost_mono 2 (hℓ y1 (by simp))
    have e1 := e sb (by simp)
    have e2 := e 8 (by simp)
    have e5 := e p (by simp)
    have e6 := e len (by simp)
    have e11 := e 2 (by simp)
    unfold printIdxCost
    omega

end NearQuarticWires.Reconstruct
