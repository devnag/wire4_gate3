import Proof.Quartic.StagePrint.CutTables

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: reduce only the signed
coefficient of a separated cut, preserving its actual affine predicate. -/
def reduceCut (modulus : ℕ) (c : MatrixScoreBatch.Cut) : MatrixScoreBatch.Cut :=
  { c with coefficient := c.coefficient % (modulus : ℤ) }

/-- `lem:print`, paper/paper.tex: the reduced coefficient
is nonnegative and strictly below the actual positive modulus. -/
theorem reduceCut_bound (modulus : ℕ) (hm : 0 < modulus)
    (c : MatrixScoreBatch.Cut) :
    (reduceCut modulus c).coefficient.natAbs < modulus := by
  have hp : (0 : ℤ) < modulus := by exact_mod_cast hm
  have h0 := Int.emod_nonneg c.coefficient (ne_of_gt hp)
  have h1 := Int.emod_lt_of_pos c.coefficient hp
  change (c.coefficient % (modulus : ℤ)).natAbs < modulus
  exact_mod_cast (show (c.coefficient % (modulus : ℤ)).natAbs < (modulus : ℤ) by
    rw [Int.natCast_natAbs, abs_of_nonneg h0]
    exact h1)

/-- `lem:print`, paper/paper.tex: the native matrix request
uses the same cuts, center transformation and dimensions, with enough bits
for both the original affine data and the reduced coefficients. -/
def reduceRequest (r : MatrixScoreBatch.Request) (modulus width : ℕ)
    (hp : r.p ≤ width) (hm : 0 < modulus) (hfit : modulus ≤ 2 ^ width) :
    MatrixScoreBatch.Request where
  d := r.d
  p := width
  cuts := r.cuts.map (reduceCut modulus)
  width := r.width
  column := r.column
  widthLe := r.widthLe
  columnFits := r.columnFits
  lengths := by
    intro c hc
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hc
    subst c
    exact r.lengths original horiginal
  fits := by
    intro c hc
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hc
    subst c
    obtain ⟨hw, ht, _⟩ := r.fits original horiginal
    have hpow : 2 ^ r.p ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hp
    exact ⟨fun w hw' => (hw w hw').trans_le hpow,
      ht.trans_le hpow, (reduceCut_bound modulus hm original).trans_le hfit⟩
  gateSquare := by simpa using r.gateSquare

/-- `lem:print`, paper/paper.tex: coefficient reduction
does not change the number of physical cut occurrences. -/
theorem reduceRequest_cuts_length (r : MatrixScoreBatch.Request)
    (modulus width : ℕ) (hp : r.p ≤ width) (hm : 0 < modulus)
    (hfit : modulus ≤ 2 ^ width) :
    (reduceRequest r modulus width hp hm hfit).cuts.length = r.cuts.length := by
  simp [reduceRequest]

/-- `lem:print`, paper/paper.tex: coefficient reduction
keeps the shared affine transformation on every actual table index. -/
theorem reduceRequest_phi (r : MatrixScoreBatch.Request)
    (modulus width : ℕ) (hp : r.p ≤ width) (hm : 0 < modulus)
    (hfit : modulus ≤ 2 ^ width) (x : ℕ) :
    (reduceRequest r modulus width hp hm hfit).phi x = r.phi x := rfl

/-- `lem:print`, paper/paper.tex: one weighted separated
cut evaluated on the literal pair of transformed assignments. -/
def cutValue (c : MatrixScoreBatch.Cut) (x y : ℕ) : ℤ :=
  c.coefficient * ((decide (c.threshold - MatrixScoreBatch.linearForm c.leftWeights x ≤
    MatrixScoreBatch.linearForm c.rightWeights y) : Bool).toNat : ℤ)

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
reducing a cut coefficient preserves its exact value modulo the modulus. -/
theorem reduceCut_value_mod (modulus : ℕ) (c : MatrixScoreBatch.Cut) (x y : ℕ) :
    cutValue (reduceCut modulus c) x y % (modulus : ℤ) =
      cutValue c x y % (modulus : ℤ) := by
  simp [cutValue, reduceCut, Int.mul_emod]

/-- `lem:print`, paper/paper.tex: a coefficient-reduced
cut list has the same exact signed sum modulo the modulus. -/
theorem reduceCuts_sum_mod (modulus : ℕ) (cuts : List MatrixScoreBatch.Cut)
    (x y : ℕ) :
    (((cuts.map (reduceCut modulus)).map (fun c => cutValue c x y)).sum) %
        (modulus : ℤ) =
      ((cuts.map (fun c => cutValue c x y)).sum) % (modulus : ℤ) := by
  induction cuts with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Int.add_emod, reduceCut_value_mod, ih, ← Int.add_emod]

end NearQuarticWires.StageRecovery
