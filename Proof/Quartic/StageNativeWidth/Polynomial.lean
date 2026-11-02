import Proof.Quartic.StageNativeWidth.SourceBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicWires NearCubicWires.WireExponent3_5
open StagePrint.NativeWidth

/-- `lem:print` and `prop:time`, paper/paper.tex: polynomial selected degree and coefficient bit bounds
control the actual proposed packed width and both native header widths. -/
theorem packedBits_polynomial (n L s D cbits d C E : ℕ)
    (hL : L ≤ 16*(n+1)^2) (hs : s ≤ 2*n) (hd : d ≤ n)
    (hD : D ≤ C*(n+1)^E) (hc : cbits ≤ C*(n+1)^E) :
    let W := packedBits L s D cbits
    let K := 1000*(C+1)^2*(n+1)^(2*E+6)
    W ≤ K ∧ W+1 ≤ K ∧ d+2*(W+1)+3 ≤ K := by
  let V := n+1
  let T := (C+1)*V^(E+2)
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hT : 1 ≤ T := by
    calc
      1 = 1*1 := rfl
      _ ≤ (C+1)*V^(E+2) := Nat.mul_le_mul (by omega) (Nat.one_le_pow _ _ hV)
  have hT2 : 1 ≤ T^2 := Nat.one_le_pow _ _ hT
  have hVT : V ≤ T := by
    have h1 : V ≤ V^(E+2) := Nat.le_self_pow (by omega) V
    exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hV2T : V^2 ≤ T :=
    (Nat.pow_le_pow_right hV (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hDT : D ≤ T := hD.trans (Nat.mul_le_mul (by omega)
    (Nat.pow_le_pow_right hV (by omega)))
  have hcT : cbits ≤ T := hc.trans (Nat.mul_le_mul (by omega)
    (Nat.pow_le_pow_right hV (by omega)))
  have hLT : L ≤ 16*T := hL.trans (Nat.mul_le_mul_left _ hV2T)
  have hsT : s ≤ 2*T := by have h := Nat.mul_le_mul_left 2 hVT; dsimp [V] at h; omega
  have hfirst : D+2 ≤ 3*T := by omega
  have hsecond : L+s+D+4 ≤ 23*T := by omega
  have hprod : (D+2)*(L+s+D+4) ≤ 69*T^2 := by
    calc
      _ ≤ (3*T)*(23*T) := Nat.mul_le_mul hfirst hsecond
      _ = _ := by ring
  have hTT : T ≤ T^2 := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) T
  have hmax : max cbits ((D+2)*(L+s+D+4)) ≤ 69*T^2 :=
    max_le (by omega) hprod
  have hW : packedBits L s D cbits ≤ 73*T^2 := by unfold packedBits; omega
  have hdT : d ≤ T^2 := by dsimp [V] at hVT; omega
  have hp : packedBits L s D cbits+1 ≤ 74*T^2 := by omega
  have hq : d+2*(packedBits L s D cbits+1)+3 ≤ 152*T^2 := by omega
  have hscale : T^2 ≤ (C+1)^2*V^(2*E+6) := by
    have he : T^2 = (C+1)^2*V^(2*E+4) := by
      dsimp [T]
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    rw [he]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hV (by omega))
  have hk : 1000*T^2 ≤ 1000*(C+1)^2*V^(2*E+6) := by
    have h := Nat.mul_le_mul_left 1000 hscale
    simpa only [Nat.mul_assoc] using h
  exact ⟨(by omega : packedBits L s D cbits ≤ 1000*T^2).trans hk,
    (by omega : packedBits L s D cbits+1 ≤ 1000*T^2).trans hk,
    (by omega : d+2*(packedBits L s D cbits+1)+3 ≤ 1000*T^2).trans hk⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual original row field width is quadratic in
original arity, independently of child or canonical role. -/
theorem nativeFieldWidth_le (r : StageTuple.RowContext) :
    r.nativeFieldWidth ≤ 16*(r.header.call.n+1)^2 := by
  have hlog : Nat.clog 2 (r.header.call.n+1) ≤ r.header.call.n+1 := by
    apply Nat.clog_le_of_le_pow
    exact Nat.lt_two_pow_self.le
  have hm := Nat.mul_le_mul_left (4*r.header.call.n+1) hlog
  unfold StageTuple.RowContext.nativeFieldWidth StageTuple.RowContext.inputFieldWidth
  nlinarith only [hm]

/-- `imp:partition`, paper/paper.tex: both actual
native half dimensions remain bounded by the original arity. -/
theorem nativeDimensions_le (r : StageTuple.RowContext) :
    PrimT.C4Geo.width r.header.prepared.starParams ≤ r.header.call.n ∧
      PrimT.C4Geo.dRow r.header.prepared.starParams ≤ r.header.call.n := by
  constructor
  · exact StagePullback.NativeRows.nativeWidth_le _
  · change r.header.prepared.starParams.leftCenterBits ≤ r.header.prepared.starParams.n
    have h := r.header.prepared.starParams.centerBits_sum
    omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the real common-generator p=W+1 and q=d+2p+3 headers
are bounded by fixed original-arity polynomials, using coefficient bit
bounds rather than syntactic formula weight or the machine register width. -/
theorem native_widths_polynomial (r : StageTuple.RowContext) (D cbits C E : ℕ)
    (hD : D ≤ C*(r.header.call.n+1)^E) (hc : cbits ≤ C*(r.header.call.n+1)^E) :
    let W := packedBits r.nativeFieldWidth (2*PrimT.C4Geo.width r.header.prepared.starParams) D cbits
    let K := 1000*(C+1)^2*(r.header.call.n+1)^(2*E+6)
    W ≤ K ∧ W+1 ≤ K ∧ PrimT.C4Geo.dRow r.header.prepared.starParams+2*(W+1)+3 ≤ K :=
  packedBits_polynomial _ _ _ _ _ _ C E (nativeFieldWidth_le r)
    (Nat.mul_le_mul_left 2 (nativeDimensions_le r).1) (nativeDimensions_le r).2 hD hc

end NearQuarticWires.StageNativeWidth
