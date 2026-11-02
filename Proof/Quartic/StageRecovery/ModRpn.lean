import Proof.Gates.Expand.Rpn

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the actual formula's
postfix arithmetic is evaluated modulo the recovery modulus at a
Boolean characteristic point, with reduction after each operation. -/
def modAlg (modulus point : ℕ) : Alg where
  c value := (value % (modulus : ℤ)).toNat
  v atom := if point.testBit atom then 1 % modulus else 0
  add left right := (left + right) % modulus
  neg value := (modulus - value) % modulus
  sub left right := (left + (modulus - right)) % modulus
  mul left right := left * right % modulus
  pow value exponent := value ^ exponent % modulus

/-- `lem:print`, paper/paper.tex: every stack value of
the actual postfix residue evaluator lies strictly below its positive
modulus, independently of unreduced formula values. -/
theorem modAlg_closed (modulus point : ℕ) (hm : 0 < modulus) :
    (modAlg modulus point).Closed modulus where
  c value := by
    have hz : (0 : ℤ) < modulus := by exact_mod_cast hm
    exact (Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hz))).mpr
      (by exact_mod_cast (Int.emod_lt_of_pos value hz))
  v atom := by
    simp only [modAlg]
    split_ifs
    · exact Nat.mod_lt _ hm
    · exact hm
  add _ _ _ _ := Nat.mod_lt _ hm
  neg _ _ := Nat.mod_lt _ hm
  sub _ _ _ _ := Nat.mod_lt _ hm
  mul _ _ _ _ := Nat.mod_lt _ hm
  pow _ _ _ := Nat.mod_lt _ hm

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
bounded postfix arithmetic gives exactly the residue of the literal
integer formula on the original Boolean atom coordinates. -/
theorem modAlg_eval (modulus point : ℕ) (hm : 0 < modulus)
    {V : ℕ} (formula : Formula V) :
    ((modAlg modulus point).eval formula : ℤ) =
      formula.eval (boolPoint (ind (NearCubicGates.Close.Expand.setOf V point))) % (modulus : ℤ) := by
  have key (value : ℕ) (integer : ℤ)
      (h : (value : ℤ) ≡ integer [ZMOD (modulus : ℤ)]) :
      ((value % modulus : ℕ) : ℤ) = integer % (modulus : ℤ) := by
    rw [Int.natCast_mod]
    exact h
  have back (value : ℕ) (integer : ℤ)
      (h : (value : ℤ) = integer % (modulus : ℤ)) :
      (value : ℤ) ≡ integer [ZMOD (modulus : ℤ)] := by
    unfold Int.ModEq
    rw [h, Int.emod_emod]
  have hzero : (modulus : ℤ) ≡ 0 [ZMOD (modulus : ℤ)] := by simp [Int.ModEq]
  have hlt (child : Formula V) : (modAlg modulus point).eval child ≤ modulus :=
    ((modAlg modulus point).eval_lt (modAlg_closed modulus point hm) child).le
  induction formula with
  | const value =>
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hm)))
  | var atom =>
      have hb : boolPoint (ind (NearCubicGates.Close.Expand.setOf V point)) atom = if point.testBit atom.val then 1 else 0 := by
        simp [boolPoint, ind, NearCubicGates.Close.Expand.setOf]
      simp only [Alg.eval, modAlg, Formula.eval, hb]
      split_ifs
      · exact key 1 1 (Int.ModEq.refl _)
      · simp
  | add left right ihl ihr =>
      exact key _ _ (by push_cast; exact (back _ _ ihl).add (back _ _ ihr))
  | neg child ih =>
      apply key
      rw [Nat.cast_sub (hlt child)]
      simpa [Formula.eval] using hzero.sub (back _ _ ih)
  | sub left right ihl ihr =>
      apply key
      rw [Nat.cast_add, Nat.cast_sub (hlt right)]
      simpa [Formula.eval, sub_eq_add_neg] using (back _ _ ihl).add (hzero.sub (back _ _ ihr))
  | mul left right ihl ihr =>
      exact key _ _ (by push_cast; exact (back _ _ ihl).mul (back _ _ ihr))
  | pow child exponent ih =>
      exact key _ _ (by push_cast; exact (back _ _ ih).pow exponent)

end NearQuarticWires.StageRecovery
