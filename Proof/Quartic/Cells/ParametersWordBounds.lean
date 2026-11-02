import Proof.Quartic.Cells.ParametersPreparationBounds
import Proof.Gates.CounterAsm.OutLen

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- The natural-number codec used by `sec:params` and `prop:time`,
paper/paper.tex, prints a value bounded
by `2^B` in at most `2B+3` cells. -/
theorem natWord_length_of_power_bound (v B : ℕ) (hv : v ≤ 2 ^ B) :
    (natWord v).length ≤ 2 * B + 3 := by
  have hlt : v < 2 ^ (B + 1) := by
    have hpos := Nat.two_pow_pos B
    rw [pow_succ]
    omega
  have hbits := NearCubicGates.Close.CounterAsm.nbl_le_of_lt' hlt (by omega)
  rw [NearCubicGates.Close.CounterAsm.natWord_len']
  omega

/-- The rational codec used in the parameter record, `prop:time`,
paper/paper.tex, has a direct numerator/denominator
bit bound, without requiring a dyadic denominator. -/
theorem ratWord_length_of_power_bounds (q : ℚ) (B : ℕ)
    (hnum : q.num.natAbs ≤ 2 ^ B) (hden : q.den ≤ 2 ^ B) :
    (ratWord q).length ≤ 4 * B + 9 := by
  have hn := natWord_length_of_power_bound q.num.natAbs B hnum
  have hd := natWord_length_of_power_bound q.den B hden
  have hs : (natWord (if q.num < 0 then 1 else 0)).length ≤ 3 := by
    split_ifs <;> decide
  simp only [ratWord, NearCubicGates.Close.Interfaces.intWord, List.length_append]
  omega

/-- Reduction of an integer quotient cannot increase either stored
integer, as used for the rational parameters of `sec:params`,
paper/paper.tex. -/
theorem divInt_size_bounds (a : ℤ) (b : ℕ) (hb : 0 < b) :
    (Rat.divInt a (b : ℤ)).num.natAbs ≤ a.natAbs ∧ (Rat.divInt a (b : ℤ)).den ≤ b := by
  constructor
  · by_cases ha : a = 0
    · simp [ha]
    · have hdiv := Rat.num_dvd a (by exact_mod_cast hb.ne' : (b : ℤ) ≠ 0)
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (Int.natAbs_dvd_natAbs.mpr hdiv)
  · have hdiv := Rat.den_dvd a (b : ℤ)
    have hn : (Rat.divInt a (b : ℤ)).den ∣ b := by exact_mod_cast hdiv
    exact Nat.le_of_dvd hb hn

/-- Dividing a rational input by a positive natural scale, as in
`eta = beta/(16 MF)` of `sec:params`, paper/paper.tex,
leaves the numerator bounded by the input numerator and multiplies the
denominator bound by at most that scale. -/
theorem div_natCast_size_bounds (q : ℚ) (d : ℕ) (hd : 0 < d) :
    (q / d).num.natAbs ≤ q.num.natAbs ∧ (q / d).den ≤ q.den * d := by
  have heq : q / (d : ℚ) = Rat.divInt q.num ((q.den * d : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    rw [div_mul_eq_div_div, q.num_div_den]
  rw [heq]
  exact divInt_size_bounds q.num (q.den * d) (Nat.mul_pos q.pos hd)

/-- The exact natural list codec of the parameter record,
`sec:params` and `prop:time`, paper/paper.tex, is bounded by its actual entry census and bit bound. -/
theorem listWord_nat_length_of_power_bounds (values : List ℕ) (B : ℕ)
    (hlen : values.length ≤ 2 ^ B) (hvalues : ∀ v ∈ values, v ≤ 2 ^ B) :
    (listWord natWord values).length ≤ (values.length + 1) * (2 * B + 3) := by
  have hflat : (values.flatMap natWord).length ≤ values.length * (2 * B + 3) := by
    induction values with
    | nil => simp
    | cons a tail ih =>
      have ha : a ≤ 2 ^ B := hvalues a (List.mem_cons_self ..)
      have ht : ∀ v ∈ tail, v ≤ 2 ^ B := fun v hv => hvalues v (List.mem_cons_of_mem _ hv)
      have hi := ih (by simp only [List.length_cons] at hlen; omega) ht
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hword := natWord_length_of_power_bound a B ha
      nlinarith only [hi, hword]
  unfold listWord
  simp only [List.length_append]
  have hhead := natWord_length_of_power_bound values.length B hlen
  nlinarith only [hflat, hhead]

end NearQuarticWires.Cells.ParameterArithmetic
