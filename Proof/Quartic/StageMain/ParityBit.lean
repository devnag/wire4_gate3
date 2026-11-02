import Proof.Quartic.StageMain.PointBit

/-!
# Selecting a parity coordinate

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. An encoded parity index contributes its
input coordinate when it lies below the arity, and false otherwise. The
parity accumulator is updated by Boolean exclusive-or.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch

def callArity : Fin VV := ⟨63, by decide⟩
def parityResult : Fin VV := ⟨64, by decide⟩
def parityIndex : Fin VV := ⟨65, by decide⟩
def parityLength : Fin VV := ⟨66, by decide⟩

def coordinateBit (n x i : ℕ) : Bool := decide (i < n) && x.testBit i

def parityChoose : St VV := .ite (.lt t3 callArity) readPointBit (.op (.zero pointBit))
def parityChooseScratch : List (Fin VV) := readPointBitScratch

theorem parityChoose_spec {C : Ctx} (a : DS VV) (hc : Cst a) (i : ℕ)
    (hi : a.env t3 = i) (hW : a.env callArity + 2 ≤ C.Wd)
    (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C parityChoose a (5 * a.env callArity + 82) (fun b =>
      b.env pointBit = (coordinateBit (a.env callArity) (a.env pointSaved) i).toNat ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b parityChooseScratch) := by
  by_cases hh : i < a.env callArity
  · have he : (Cnd.lt t3 callArity).eval a = true := by simp [Cnd.eval, hi, hh]
    refine Hs.mono (Hs.iteT (show t3 ≠ callArity by decide) he
      (readPointBit_spec a hc i hi (by omega) hpoint)) (by omega) ?_
    rintro b ⟨bb, bp, bw, bo, bc, bf⟩
    exact ⟨by simpa [coordinateBit, hh] using bb, bp, bw, bo, bc, bf⟩
  · have he : (Cnd.lt t3 callArity).eval a = false := by simp [Cnd.eval, hi, hh]
    refine Hs.mono (Hs.iteF (show t3 ≠ callArity by decide) he (hs_zero C pointBit a)) (by omega) ?_
    rintro b rfl
    exact ⟨by simp [coordinateBit, hh], rfl, rfl, rfl, hc.set _ _ (by decide),
      (Fr.set _ _ (by decide)).toS⟩

def parityXor : St VV := .ite (.eq parityResult pointBit)
  (.op (.zero parityResult)) (.op (.copy parityResult v1))

theorem parityXor_spec {C : Ctx} (a : DS VV) (hc : Cst a) (old bit : Bool)
    (ho : a.env parityResult = old.toNat) (hb : a.env pointBit = bit.toNat) :
    Hs C parityXor a 2 (fun b =>
      b.env parityResult = (xor old bit).toNat ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b [parityResult]) := by
  cases old <;> cases bit
  all_goals
    first
    | have he : (Cnd.eq parityResult pointBit).eval a = true := by simp [Cnd.eval, ho, hb]
      refine Hs.mono (Hs.iteT (show parityResult ≠ pointBit by decide) he (hs_zero C parityResult a)) le_rfl ?_
      rintro b rfl
      exact ⟨by simp, rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
    | have he : (Cnd.eq parityResult pointBit).eval a = false := by simp [Cnd.eval, ho, hb]
      refine Hs.mono (Hs.iteF (show parityResult ≠ pointBit by decide) he
        (hs_copy C parityResult v1 a (by decide))) le_rfl ?_
      rintro b rfl
      exact ⟨by simp [hc.one], rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩

end NearQuarticWires.StageMain
