import Proof.Quartic.StagePrint.OriginalChildMachine

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: every actual active child field is bounded in the
original total magnitude, including the signed shifted target. -/
theorem active_child_fields_natAbs_bound (ws : List ℤ) (sh bit i : ℕ)
    (hsh : sh < totalL ws) (hbit : 2 ^ bit ≤ totalL ws) :
    ∀ z ∈ childL ws sh bit i, z.natAbs ≤ 4 * totalL ws + ws.length + 2 := by
  intro z hz
  rw [childL_eq] at hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
    have hjlt : j < ws.length := List.mem_range.mp hj
    have hmem : ws.getD j 0 ∈ ws := by
      rw [List.getD_eq_getElem _ _ hjlt]
      exact List.getElem_mem hjlt
    have hw := natAbs_le_totalL hmem
    have hl := litW_le ws bit i j
    unfold fieldJ
    split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega
  · have hzval := List.mem_singleton.mp hz
    subst z
    let A := 2 * 2 ^ bit * (sh / 2 ^ bit + 1) + 1
    have hdiv : sh / 2 ^ bit * 2 ^ bit ≤ sh := Nat.div_mul_le_self sh _
    have hA : A ≤ 4 * totalL ws + 1 := by dsimp only [A]; nlinarith only [hdiv, hbit, hsh]
    have hN := (negSum_le ws bit i ws.length).trans (sumRange_le ws ws.length le_rfl)
    rw [sum_odd] at hN
    have he : 2 * (2 : ℤ) ^ bit * ((sh / 2 ^ bit + 1 : ℕ) : ℤ) + 1 -
        (negSum ws bit i ws.length : ℤ) =
        (A : ℤ) - (negSum ws bit i ws.length : ℤ) := by
      dsimp only [A]
      push_cast
      ring
    rw [he]
    have hb : |(A : ℤ) - (negSum ws bit i ws.length : ℤ)| ≤
        ((4 * totalL ws + ws.length + 2 : ℕ) : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    rw [← Int.natCast_natAbs] at hb
    exact_mod_cast hb

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: every row actually emitted by the original strict
compiler fits its original magnitude width, including both constant
outcomes and every active-bit child. -/
theorem compileL_fields_natAbs_lt (ws : List ℤ) (target : ℤ) (W : ℕ)
    (hW : 4 * totalL ws + 2 * ws.length + 4 ≤ 2 ^ W) :
    ∀ row ∈ compileL ws target, ∀ z ∈ row, z.natAbs < 2 ^ W := by
  intro row hrow z hz
  unfold compileL at hrow
  split_ifs at hrow with hnegative hlarge
  · have hr : row = zeroL ws.length 0 := by simpa only [List.mem_singleton] using hrow
    subst row
    simp only [zeroL, List.mem_append, List.mem_replicate, List.mem_singleton] at hz
    rcases hz with ⟨_, rfl⟩ | rfl
    · change (0 : ℕ) < 2 ^ W
      omega
    · change (0 : ℕ) < 2 ^ W
      omega
  · have hr : row = zeroL ws.length 1 := by simpa only [List.mem_singleton] using hrow
    subst row
    simp only [zeroL, List.mem_append, List.mem_replicate, List.mem_singleton] at hz
    rcases hz with ⟨_, rfl⟩ | rfl
    · change (0 : ℕ) < 2 ^ W
      omega
    · change (1 : ℕ) < 2 ^ W
      omega
  · obtain ⟨bit, _, hrow⟩ := List.mem_flatMap.mp hrow
    obtain ⟨i, hi, hchild⟩ := List.mem_filterMap.mp hrow
    split_ifs at hchild with hactive
    · have he : childL ws (target + negMassL ws).toNat bit i = row := Option.some.inj hchild
      rw [← he] at hz
      have hil : i < ws.length := List.mem_range.mp (List.mem_reverse.mp hi)
      have hmem : ws.getD i 0 ∈ ws := by
        rw [List.getD_eq_getElem _ _ hil]
        exact List.getElem_mem hil
      have hpow : 2 ^ bit ≤ (ws.getD i 0).natAbs := by
        by_contra h
        have hf := Nat.testBit_eq_false_of_lt (by omega : (ws.getD i 0).natAbs < 2 ^ bit)
        rw [hf] at hactive
        contradiction
      have hbit : 2 ^ bit ≤ totalL ws := hpow.trans (natAbs_le_totalL hmem)
      have hsh : (target + negMassL ws).toNat < totalL ws := by omega
      have hb := active_child_fields_natAbs_bound ws _ bit i hsh hbit z hz
      omega

/-- `imp:pullback` and `lem:print`, paper/paper.tex: each actual original-child row has the exact signed
field fit needed by the canonical affine row input, without changing W. -/
theorem originalChild_compile_fields_fit (r : StagePrint.OriginalChildRequest) :
    ∀ row ∈ compileL r.weights r.target, ∀ z ∈ row,
      SInt.encS z < 2 ^ (r.W + 1) := by
  intro row hr z hz
  exact SInt.encS_lt (compileL_fields_natAbs_lt r.weights r.target r.W r.weights_fit row hr z hz)

end NearQuarticWires.Cells.ParameterArithmetic
