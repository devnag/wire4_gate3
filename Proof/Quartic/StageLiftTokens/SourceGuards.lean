import Proof.Quartic.StageLiftTokens.SourceState
import Proof.Quartic.StageLiftTokens.CoefficientBounds

/-!
# Guards derived from the actual retained source

`lem:print` and `prop:time`, paper/paper.tex: every original atom address, source horizon and binary
coefficient length is bounded by the finite residue-entry envelope.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicGates.Close.Cells StageLift StageCert.Tokens

variable {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2} {a : DS VV MM} {E : ℕ}

theorem SourceReady.width_five (h : SourceReady C r a E) : 5≤C.Wd :=
  source_width E C.Wd h.envelope_pos h.width

theorem SourceReady.atom_room (h : SourceReady C r a E) :
    17*(Builder.allGates r.child.call).length<2^C.Wd := by
  apply source_count_capacity E C.Wd _ h.envelope_pos h.width
  have hg := h.occurrences_bound
  nlinarith [Nat.mul_self_le_mul_self (show 1≤E+1 by omega)]

theorem SourceReady.atom_bits (h : SourceReady C r a E) :
    ∀g<(Builder.allGates r.child.call).length,∀edge corner,
      natBitLength (cornerRoleCode edge corner*(Builder.allGates r.child.call).length+g)≤ sourceBits E := by
  intro g hg edge corner
  have hr : cornerRoleCode edge corner<17 := by
    rw [←cornerRoleCode_eq]
    exact (Cells.offsetIndex 4 (Cells.cornerRole (by decide : 0<4) edge corner)).isLt
  apply source_small_bits E _ h.envelope_pos
  have hG := h.occurrences_bound
  nlinarith [Nat.mul_self_le_mul_self (show 1≤E+1 by omega)]

theorem SourceReady.bits_room (h : SourceReady C r a E) :
    sourceBits E+2<2^C.Wd := source_bits_capacity E C.Wd h.envelope_pos h.width

theorem SourceReady.witness_room (h : SourceReady C r a E) :
    r.child.selected.1.k+(r.child.selected.1.J+1)*(Builder.allGates r.child.call).length≤2^C.Wd := by
  rw [←source_witness_prefix_length r.child.call r.child.selected.1 r.child.witness]
  exact (source_count_capacity E C.Wd _ h.envelope_pos h.width (by
    have hl := h.witness_length
    omega)).le

theorem SourceReady.chain_room (h : SourceReady C r a E) : r.child.selected.1.J≤2^C.Wd := by
  exact (source_count_capacity E C.Wd _ h.envelope_pos h.width (by
    have hj := h.chains_bound
    have hpow := Nat.le_self_pow (by decide : 3≠0) (E+1)
    omega)).le

theorem SourceReady.rate_room (h : SourceReady C r a E) (row : ℕ) :
    (if row=0 then 1 else r.child.selected.1.factors.getD (row-1) 0)<2^C.Wd := by
  apply lt_of_le_of_lt (source_rate_bound _ E row h.factors_bound)
  exact Nat.pow_lt_pow_right (by decide) (by have hw := h.width; nlinarith)

theorem SourceReady.factor_length (_h : SourceReady C r a E) :
    r.child.selected.1.factors.length=r.child.selected.1.J-1 := by
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  rw [hs.factors_eq]
  simp only [NearCubicGates.Close.Counter.chainFactors,List.length_map,List.length_range]

def linearSourceCost (E : ℕ) : ℕ := 10^6*(E+1)^4

theorem score_cost_le (G E : ℕ) (hG : G≤E) :
    G*(8*(40+160*sourceBits E+640)+60)+40≤linearSourceCost E := by
  unfold sourceBits linearSourceCost
  nlinarith [Nat.mul_self_le_mul_self (show E≤E+1 by omega),sq_nonneg ((E+1)^2)]

theorem digit_cost_le (G E n f : ℕ) (hG : G≤E) (hn : n≤(E+1)^3) (hf : f≤E) :
    G*(12*n+6*f+8*(40*sourceBits E+160*sourceBits E+640)+160)+40≤linearSourceCost E := by
  unfold sourceBits linearSourceCost
  have hprod : G*(12*n+6*f+8*(40*(10*(E+1)^2)+160*(10*(E+1)^2)+640)+160)≤
      E*(12*(E+1)^3+6*E+8*(40*(10*(E+1)^2)+160*(10*(E+1)^2)+640)+160) :=
    Nat.mul_le_mul hG (by omega)
  nlinarith [sq_nonneg ((E+1)^2)]

end NearQuarticWires.StageLiftTokens
