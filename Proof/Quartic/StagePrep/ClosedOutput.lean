import Proof.Gates.Dispatch.Zero

/-!
# The exact constant-call output program

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires

/-- The raw zero-wire output word of `sec:params`,
paper/paper.tex. -/
def closedZeroWord (v : ℚ) : List Bool := false :: outputWord (v, 0)

/-- The total length of the three exact outputs of
`sec:params`, paper/paper.tex. -/
def closedZeroWordLen : ℕ :=
  (closedZeroWord 0).length + (closedZeroWord 1).length + (closedZeroWord (1 / 2)).length

open AE

/-- The constant-call computation of `sec:params`,
paper/paper.tex, handles repeated parity indices. -/
def closedZeroOutput : St VV :=
  .seq oddP (.seq (.ite (.eq vTAG v1) (assign oC (mod (add (var vTB1) (var vTB2)) (lit 2)))
      (.ite (.eq oODD v1) (assign oC (lit 2)) (assign oC (var vTB1))))
    (.ite (.eq oC vZ) (emitL (closedZeroWord 0))
      (.ite (.eq oC v1) (emitL (closedZeroWord 1)) (emitL (closedZeroWord (1 / 2))))))

/-- The exact constant-call program of `sec:params`,
paper/paper.tex, has polynomial cost in the
original encoded call and reads no witness bit. -/
theorem closedZeroOutput_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (hadm : c.Admitted B1 B2) (a : DS VV) (hc : Cst a)
    (hpo : ParseOut c a) (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C closedZeroOutput a
      (oddCostT C.cw.length c.parity.length C.Wd + 2 * closedZeroWordLen + 50)
      (fun b => b.out = a.out ++ closedZeroWord (zval c) ∧
        Cst b ∧ b.wq = a.wq ∧ FrS a b zoT) := by
  obtain ⟨h4, -, -, -, hpar, hall, -⟩ := hadm
  have h4W : 4 < 2 ^ C.Wd := lt_of_lt_of_le (by norm_num : 4 < 2 ^ 3)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hx.hs (Hs.then (oddP_spec c a hc hpo hcw hW hL) (fun b1 ⟨p1, p2, p3, p4, p5⟩ k1 hk1 => ?_))
  have b1T : b1.env vTAG = kindTag c.kind := by simp (disch := decide) only [p5.ev]; exact hpo.tag
  have b1T1 : b1.env vTB1 = (c.first.table.getD 0 false).toNat := by
    simp (disch := decide) only [p5.ev]; exact hpo.c1.tb
  have b1T2 : b1.env vTB2 = (c.second.table.getD 0 false).toNat := by
    simp (disch := decide) only [p5.ev]; exact hpo.c2.tb
  have hb1 : (c.first.table.getD 0 false).toNat ≤ 1 := Bool.toNat_le _
  have hb2 : (c.second.table.getD 0 false).toNat ≤ 1 := Bool.toNat_le _
  -- the selector
  set sel : ℕ := if c.kind = .pair then ((c.first.table.getD 0 false).toNat + (c.second.table.getD 0 false).toNat) % 2
    else if (∃ x ∈ c.parity, c.parity.count x % 2 = 1) then 2 else (c.first.table.getD 0 false).toNat with hsel
  have step : Hs C (.ite (.eq vTAG v1) (assign oC (.mod (.add (.var vTB1) (.var vTB2)) (.lit 2)))
      (.ite (.eq oODD v1) (assign oC (.lit 2)) (assign oC (.var vTB1)))) b1 30 (fun g => g.env oC = sel ∧
        g.out = b1.out ∧ g.wq = b1.wq ∧ Cst g ∧ AsgFr b1 g oC) := by
    refine Hs.ite (show vTAG ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hk : c.kind = .pair := (kindTag_eq_one _).1 (by rw [← b1T]; simpa [Cnd.eval, p2.one] using he)
      refine Hs.mono (assign_spec oC (by decide) (by decide) (.mod (.add (.var vTB1) (.var vTB2)) (.lit 2)) b1
        (by aevar) (by aevar) p2 (by aeok [b1T1, b1T2])) (by simp [AE.cost]) ?_
      rintro g ⟨g1, g2, g3, g4, g5, g6⟩
      exact ⟨by rw [g1, hsel, if_pos hk]; simp [AE.eval, b1T1, b1T2], g5, g4, g6, g2⟩
    · have hk : c.kind ≠ .pair := fun h => by
        have : b1.env vTAG = 1 := by rw [b1T, h]; rfl
        simp [Cnd.eval, p2.one, this] at he
      refine Hs.ite (show oODD ≠ v1 by decide) (fun he2 => ?_) (fun he2 => ?_)
      · have ho : ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by
          have : b1.env oODD = 1 := by simpa [Cnd.eval, p2.one] using he2
          rw [p1] at this; exact (bnat_eq_one _).1 this
        refine Hs.mono (assign_spec oC (by decide) (by decide) (.lit 2) b1 (by aevar) (by aevar) p2 (by aeok []))
          (by simp [AE.cost]) ?_
        rintro g ⟨g1, g2, g3, g4, g5, g6⟩
        exact ⟨by rw [g1, hsel, if_neg hk, if_pos ho]; rfl, g5, g4, g6, g2⟩
      · have ho : ¬ ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by
          intro h
          have : b1.env oODD = 1 := by rw [p1]; exact bnat_one_of h
          simp [Cnd.eval, p2.one, this] at he2
        refine Hs.mono (assign_spec oC (by decide) (by decide) (.var vTB1) b1 (by aevar) (by aevar) p2 (by trivial))
          (by simp [AE.cost]) ?_
        rintro g ⟨g1, g2, g3, g4, g5, g6⟩
        exact ⟨by rw [g1, hsel, if_neg hk, if_neg ho]; simp [AE.eval, b1T1], g5, g4, g6, g2⟩
  refine Hs.then step (fun b2 ⟨q1, q2, q3, q4, q5⟩ k2 hk2 => ?_)
  -- the emitted word
  have hz : closedZeroWord (zval c) = (if sel = 0 then closedZeroWord 0 else if sel = 1 then closedZeroWord 1 else closedZeroWord (1 / 2)) := by
    rw [hsel]
    unfold zval
    cases hk : c.kind with
    | single =>
      have hp : c.parity = [] := hpar (by simp [hk])
      have ho : ¬ ∃ x ∈ c.parity, c.parity.count x % 2 = 1 := by rw [hp]; simp
      cases c.first.table.getD 0 false <;> simp [ho]
    | pair =>
      cases c.first.table.getD 0 false <;> cases c.second.table.getD 0 false <;> simp
    | parity =>
      by_cases ho : ∃ x ∈ c.parity, c.parity.count x % 2 = 1
      · simp [ho]
      · cases c.first.table.getD 0 false <;> simp [ho]
  have hsel3 : sel ≤ 2 := by
    rw [hsel]; split_ifs
    · omega
    · omega
    · exact le_trans hb1 (by norm_num)
  have hzl : ∀ v, 1 ≤ (closedZeroWord v).length := fun v => by simp [closedZeroWord]
  have l0 := hzl 0
  have l1 := hzl 1
  have l2 := hzl (1 / 2)
  refine Hs.last (Hs.ite (show oC ≠ vZ by decide) (fun he => ?_) (fun he => ?_)) (fun g ⟨g1, g2, g3, g4⟩ k3 hk3 =>
    ⟨⟨by rw [g1, q2, p4, ← hz], g2, by rw [g3, q3, p3],
      FrS.trans (p5.weaken (by decide)) (FrS.trans (q5.toS _ (by decide) (by decide)) (g4.toS.weaken (by decide)))⟩,
      by omega⟩)
    (R1 := fun g => g.out = b2.out ++ (if sel = 0 then closedZeroWord 0 else if sel = 1 then closedZeroWord 1 else closedZeroWord (1 / 2)) ∧ Cst g ∧
      g.wq = b2.wq ∧ Fr b2 g [vJ]) (t := 2 * closedZeroWordLen + 2)
  · have h0 : sel = 0 := by rw [← q1]; simpa [Cnd.eval, q4.z] using he
    refine Hs.mono (emitL_spec (closedZeroWord 0) b2) (by unfold closedZeroWordLen; omega) ?_
    rintro g ⟨g1, g2, g3, g4⟩
    have hcg : Cst g := Cst.of_fr q4 g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact q4.pos)
    exact ⟨by rw [g1, if_pos h0], hcg, g3, g4⟩
  · have h0 : sel ≠ 0 := by rw [← q1]; simpa [Cnd.eval, q4.z] using he
    refine Hs.ite (show oC ≠ v1 by decide) (fun he2 => ?_) (fun he2 => ?_)
    · have h1 : sel = 1 := by rw [← q1]; simpa [Cnd.eval, q4.one] using he2
      refine Hs.mono (emitL_spec (closedZeroWord 1) b2) (by unfold closedZeroWordLen; omega) ?_
      rintro g ⟨g1, g2, g3, g4⟩
      have hcg : Cst g := Cst.of_fr q4 g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact q4.pos)
      exact ⟨by rw [g1, if_neg h0, if_pos h1], hcg, g3, g4⟩
    · have h1 : sel ≠ 1 := by rw [← q1]; simpa [Cnd.eval, q4.one] using he2
      refine Hs.mono (emitL_spec (closedZeroWord (1 / 2)) b2) (by unfold closedZeroWordLen; omega) ?_
      rintro g ⟨g1, g2, g3, g4⟩
      have hcg : Cst g := Cst.of_fr q4 g4 (by decide) (by rw [g4 vPOS (by decide), g2]; exact q4.pos)
      exact ⟨by rw [g1, if_neg h0, if_neg h1], hcg, g3, g4⟩

end NearQuarticWires.StagePrep
