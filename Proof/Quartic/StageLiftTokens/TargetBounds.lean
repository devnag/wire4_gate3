import Proof.Quartic.StageLiftTokens.SourceGuards

/-!
# Literal normalized target records

`lem:residue` and Step 3, paper/paper.tex: both score records and every circuit-major digit record
are read from the actual normalized index bank. Their values have
polynomial binary length even when the original signed input is large.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicGates.Close.Cells StageLift

variable {B1 B2 : ℕ}

theorem index_length (r : Greedy.PrintRequest B1 B2) :
    (normalizedPrintIndex r).length=12+2*r.child.selected.1.J := by
  simp only [normalizedPrintIndex,List.length_append,List.length_singleton,
    List.length_ofFn,List.length_map,printResidueList_length,print_digit_count,Algorithm.traceOrder]
  omega

theorem actual_modulus_pos (r : Greedy.PrintRequest B1 B2) : 0<r.prime^r.child.selected.1.e :=
  pow_pos (Reconstruct.PrintRequest.prime_prime r).pos _

theorem normalized_score_value (r : Greedy.PrintRequest B1 B2) (j : Fin 2) :
    (((normalizedPrintIndex r).getD (10+2*r.child.selected.1.J+j.val) 0 : ℕ) : ℤ)=
      r.residues j % (r.prime^r.child.selected.1.e : ℤ) := by
  rw [←print_digit_count r,normalizedPrintIndex_score,Int.toNat_of_nonneg]
  exact Int.emod_nonneg _ (ne_of_gt (by exact_mod_cast actual_modulus_pos r))

theorem normalized_digit_value (r : Greedy.PrintRequest B1 B2) (j : Fin 2)
    (row : Fin (r.child.selected.1.J-1+1)) :
    ((((normalizedPrintIndex r).getD (10+j.val*r.child.selected.1.J+row.val) 0)%r.prime : ℕ) : ℤ)=
      (r.digits j row % (r.prime^r.child.selected.1.e : ℤ)) % (r.prime : ℤ) := by
  have hi := normalizedPrintIndex_digit r j row
  simp only [print_chain_length] at hi
  rw [hi,Int.natCast_mod,Int.toNat_of_nonneg]
  exact Int.emod_nonneg _ (ne_of_gt (by exact_mod_cast actual_modulus_pos r))

theorem SourceReady.target_room {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} {E : ℕ} (h : SourceReady C r a E) :
    2*r.child.selected.1.J+11<2^C.Wd := by
  apply source_count_capacity E C.Wd _ h.envelope_pos h.width
  have hj:=h.chains_bound
  have hp := Nat.le_self_pow (by decide : 3≠0) (E+1)
  omega

theorem SourceReady.prime_room {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} {E : ℕ} (h : SourceReady C r a E) :
    2*r.prime≤2^C.Wd := by
  apply (source_count_capacity E C.Wd _ h.envelope_pos h.width ?_).le
  have hj:=h.prime_bound
  have hp := Nat.le_self_pow (by decide : 3≠0) (E+1)
  omega

theorem SourceReady.prime_bits {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} {E : ℕ} (h : SourceReady C r a E) :
    natBitLength r.prime≤ sourceBits E := by
  apply source_small_bits E _ h.envelope_pos
  have hj:=h.prime_bound
  have hp := Nat.le_self_pow (by decide : 3≠0) (E+1)
  omega

theorem SourceReady.score_bits {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} {E : ℕ} (h : SourceReady C r a E) (j : Fin 2) :
    natBitLength ((normalizedPrintIndex r).getD (10+2*r.child.selected.1.J+j.val) 0)≤ sourceBits E := by
  rw [←print_digit_count r,normalizedPrintIndex_score]
  have hmod : (r.residues j % (r.prime^r.child.selected.1.e : ℤ)).toNat≤r.prime^r.child.selected.1.e := by
    apply Int.toNat_le.mpr
    exact (Int.emod_lt_of_pos _ (by exact_mod_cast actual_modulus_pos r)).le
  exact (codec_nbl_mono hmod).trans (source_modulus_bits E _ _ h.envelope_pos h.prime_bound h.exponent_bound)

end NearQuarticWires.StageLiftTokens
