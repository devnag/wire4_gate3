import Proof.Quartic.StageColumns.Request

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.RepairOrdinary

/-- `imp:partition` and `lem:print`, paper/paper.tex: the common native code has no more free row bits
than dense half coordinates. -/
theorem native_dimension_le_width (P : StarParams) :
    PrimT.C4Geo.dRow P≤PrimT.C4Geo.width P := by
  unfold PrimT.C4Geo.dRow PrimT.C4Geo.width StarParams.leftCenterBits PrimT.C4Geo.hL
  have hm:=Nat.mul_le_mul_left (P.r/2) (Nat.sub_le P.b P.s)
  omega

private theorem twice_add_one_le_power (s : ℕ) (hs : 3 ≤ s) : 2*s+1 ≤ 2^s := by
  induction s,hs using Nat.le_induction with
  | base=>norm_num
  | succ s hs ih=>
      rw [pow_succ]
      nlinarith

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual Hamming-code half satisfies the native
printer's two-coordinate-per-row-bit condition, including the
smallest admitted block size. -/
theorem native_width_le_two_dimensions (P : StarParams) :
    PrimT.C4Geo.width P≤2*PrimT.C4Geo.dRow P := by
  have hs2 : 2≤P.s := by
    apply Nat.le_log_of_pow_le (by decide : 1<2)
    have hdiv : 4≤P.n/P.r := (Nat.le_div_iff_mul_le P.r_pos).mpr (by simpa [Nat.mul_comm] using P.four_r_le_n)
    norm_num
    omega
  have hhalf:=P.r_half_add
  have hrb:=P.r_mul_b_le
  have hsb:=P.s_le_b
  have hsub : P.b-P.s+P.s=P.b := Nat.sub_add_cancel hsb
  by_cases hs : P.s=2
  · have hb : P.b=3 := by have h:=P.b_succ;rw [hs] at h;norm_num at h;omega
    have hfree : P.r≤P.n-P.r*P.b := by
      have hn:=Nat.sub_add_cancel hrb
      rw [hb] at hn ⊢
      nlinarith [P.four_r_le_n]
    rw [hb] at hfree
    unfold PrimT.C4Geo.width PrimT.C4Geo.dRow StarParams.leftCenterBits PrimT.C4Geo.hL
    rw [hb,hs]
    norm_num
    omega
  · have hs3 : 3≤P.s := by omega
    have hp:=twice_add_one_le_power P.s hs3
    have hb : 2*P.s≤P.b := by have h:=P.b_succ;omega
    have hparts : P.b≤2*(P.b-P.s) := by omega
    have hm:=Nat.mul_le_mul_left (P.r/2) hparts
    have hm' : P.r/2*P.b≤2*(P.r/2*(P.b-P.s)) := by
      calc P.r/2*P.b≤P.r/2*(2*(P.b-P.s)):=hm
        _=2*(P.r/2*(P.b-P.s)):=by ring
    unfold PrimT.C4Geo.width PrimT.C4Geo.dRow StarParams.leftCenterBits PrimT.C4Geo.hL
    omega

/-- `lem:print`, paper/paper.tex: every actual
common-generator column has exactly the selected dense bit width. -/
theorem native_column_fits (P : StarParams) (j : ℕ) :
    (PrimT.C4Geo.cols P).getD j 0<2^PrimT.C4Geo.width P := by
  by_cases hj : j<PrimT.C4Geo.dRow P
  · have he : (PrimT.C4Geo.cols P).getD j 0=
        CanonicalBinary.bitsValue (PrimT.C4Geo.colBits P j) := by
      unfold PrimT.C4Geo.cols
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using hj)]
      simp only [List.getElem_map,List.getElem_range]
    rw [he]
    have h:=PrimAsm.ParseNat.bitsValue_lt (PrimT.C4Geo.colBits P j)
    simpa only [PrimT.C4Geo.colBits,List.length_ofFn] using h
  · have hl : (PrimT.C4Geo.cols P).length=PrimT.C4Geo.dRow P := by simp [PrimT.C4Geo.cols]
    rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.two_pow_pos _

end NearQuarticWires.StagePrint
