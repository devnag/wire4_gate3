import Proof.Quartic.StageGreedyEntry.HeaderWF
import Proof.Quartic.StageGreedyEntry.FormatBound
import Proof.Quartic.Control.GammaControl

/-!
# The common header from the formatted entry: the delivered extractor and its budget

Paper: `lem:print`, paper/paper.tex, and `prop:time`.

`headerExtract` is the header word function with its budget `2 hdrCostOf r + 2`. Its run is linear in the formatted
entry, whose length is at most the formatter's budget plus one (`Control.output_length_le`, `formatter_bound`), and
quadratic in the values read: the arity, the selected `r, b, s` (at most `n`), the two base header values after the
arity (polynomial in `n`) and the stack width (polynomial in the sizing magnitude, hence in `n`). So the budget is
at most `K (n+1)^e (Uocc^{2D} + 1)` (`headerExtract_bound`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open StagePrint

variable {B1 B2 : ℕ}

theorem hdRdCost_le (x : ℕ) : hdRdCost x ≤ 400 * (x + 1) ^ 2 := by
  unfold hdRdCost
  have h1 := hd_two_pow_nbl_le x
  have h2 := hd_nbl_le_self x
  have h3 : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (80 * x + 120) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

theorem hdWrCost_le (v : ℕ) : hdWrCost v ≤ 2400 * (v + 1) ^ 2 := by
  unfold hdWrCost
  have h2 := hd_nbl_le_self v
  have h3 : (natBitLength v + 10) * (100 * v + 200) ≤ (v + 11) * (100 * v + 200) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem hd_width_le (P : StarParams) : PrimT.C4Geo.width P ≤ P.n := by
  have h1 := P.r_mul_b_le
  have h2 : 2 * (P.r / 2 * P.b) ≤ P.r * P.b := by
    have h : 2 * (P.r / 2) ≤ P.r := Nat.mul_div_le P.r 2
    calc 2 * (P.r / 2 * P.b) = 2 * (P.r / 2) * P.b := by ring
      _ ≤ P.r * P.b := Nat.mul_le_mul_right _ h
  have h4 := P.four_r_le_n
  have h5 := P.two_le_r
  show P.r / 2 * P.b + (P.n - P.r * P.b + 1) / 2 ≤ P.n
  omega

/-- The stack width is at most quadratic in the sizing magnitude of the entry. -/
theorem hd_stackWidth_le (r : GreedyEntry.Request B1 B2) :
    r.termRequest.stackWidth ≤ 3 * (EntryFormat.ofGreedy r).sizingMagnitude ^ 2 +
      (EntryFormat.ofGreedy r).sizingMagnitude + 4 := by
  obtain ⟨z, hz⟩ : ∃ z, z = (EntryFormat.ofGreedy r).sizingMagnitude := ⟨_, rfl⟩
  rw [← hz]
  have hzs := hz
  unfold EntryFormat.Request.sizingMagnitude at hzs
  simp only [] at hzs
  have hw := hd_width_le r.rowContext.header.prepared.starParams
  change PrimT.C4Geo.width r.rowContext.header.prepared.starParams ≤ r.source.child.call.n at hw
  change NativeWidth.packedBits r.rowContext.nativeFieldWidth
    (2 * PrimT.C4Geo.width r.rowContext.header.prepared.starParams) r.degree r.coefficientBits ≤ _
  change z = 4 * (r.source.child.call.n + 1) ^ 2 + r.source.child.call.n + 20 +
    ((r.degree + 2) * (r.rowContext.nativeFieldWidth + 2 * ((r.source.child.call.n + 1) / 2) + r.degree + 4) +
      r.coefficientBits + r.source.child.call.n + r.rowContext.nativeFieldWidth + r.degree + 30) +
    natBitLength (EntryFormat.ofGreedy r).word.length + natBitLength r.modulus + natBitLength r.index.val +
    natBitLength r.degree + 100 at hzs
  unfold NativeWidth.packedBits
  generalize hD : r.degree = D at hzs ⊢
  generalize hL : r.rowContext.nativeFieldWidth = L at hzs ⊢
  generalize hwd : PrimT.C4Geo.width r.rowContext.header.prepared.starParams = w at hw ⊢
  generalize hn : r.source.child.call.n = n at hzs hw
  generalize hc : r.coefficientBits = c at hzs ⊢
  have hsplit : (D + 2) * (L + 2 * w + D + 4) = (D + 2) * (L + D + 4) + (D + 2) * (2 * w) := by ring
  have hA : (D + 2) * (L + D + 4) ≤ (D + 2) * (L + 2 * ((n + 1) / 2) + D + 4) :=
    Nat.mul_le_mul_left _ (by omega)
  have hD2 : D + 2 ≤ z := by
    have : D + 2 ≤ (D + 2) * (L + 2 * ((n + 1) / 2) + D + 4) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hB : (D + 2) * (2 * w) ≤ z * (2 * z) := Nat.mul_le_mul hD2 (by omega)
  have hzz : z * (2 * z) = 2 * z ^ 2 := by ring
  omega

theorem hd_clog_le_succ (n : ℕ) : Nat.clog 2 (n + 1) ≤ n + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

/-- The selected `r`, `b`, `s` are at most the arity. -/
theorem hd_selected_rbs_le (r : GreedyEntry.Request B1 B2) :
    r.source.child.selected.1.r ≤ r.source.child.call.n ∧ r.source.child.selected.1.b ≤ r.source.child.call.n ∧
      r.source.child.selected.1.s ≤ r.source.child.call.n + 1 := by
  have hs := Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hb : hs.starParams.b = r.source.child.selected.1.b := Cells.ParameterRules.star_b hs
  have hss : hs.starParams.s = r.source.child.selected.1.s := Cells.ParameterRules.star_s hs
  have hr : hs.starParams.r = r.source.child.selected.1.r := rfl
  have hn : hs.starParams.n = r.source.child.call.n := rfl
  have h4 := hs.starParams.four_r_le_n
  have h2 := hs.starParams.two_le_r
  have hpow : 2 ^ hs.starParams.s ≤ hs.starParams.n / hs.starParams.r + 1 :=
    Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have hdiv : hs.starParams.n / hs.starParams.r ≤ hs.starParams.n := Nat.div_le_self _ _
  have hslt : hs.starParams.s < 2 ^ hs.starParams.s := Nat.lt_two_pow_self
  have hbdef : hs.starParams.b = 2 ^ hs.starParams.s - 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← hr, ← hn]; omega
  · rw [← hb, ← hn]; omega
  · rw [← hss, ← hn]; omega

/-- **The header extractor** of the sub-target: the formatted entry to the framed common header. -/
noncomputable def headerExtract (B1 B2 : ℕ) :
    (budget : GreedyEntry.Request B1 B2 → ℕ) ×
      WordFunction (GreedyEntry.Request B1 B2) (fun r => frame r.termRequest.word)
        (fun r => frame (StageGreedyCollector.globalHeader r.source)) budget :=
  ⟨_, headerWF B1 B2⟩

/-- The cost of the header program: linear in the formatted entry, quadratic in the values read. -/
theorem hdrCost_le (L n x1 x2 r b s W : ℕ) :
    hdrCost L n x1 x2 r b s W ≤ 92 * L + 60 + 14800 * (n + x1 + x2 + r + b + s + W + 2) ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M, M = n + x1 + x2 + r + b + s + W + 2 := ⟨_, rfl⟩
  rw [← hM]
  have sq : ∀ x, x + 1 ≤ M → (x + 1) ^ 2 ≤ M ^ 2 := fun x h => Nat.pow_le_pow_left h 2
  have a1 := (hdRdCost_le n).trans (Nat.mul_le_mul_left 400 (sq n (by omega)))
  have a2 := (hdRdCost_le x1).trans (Nat.mul_le_mul_left 400 (sq x1 (by omega)))
  have a3 := (hdRdCost_le x2).trans (Nat.mul_le_mul_left 400 (sq x2 (by omega)))
  have a4 := (hdRdCost_le r).trans (Nat.mul_le_mul_left 400 (sq r (by omega)))
  have a5 := (hdRdCost_le b).trans (Nat.mul_le_mul_left 400 (sq b (by omega)))
  have a6 := (hdRdCost_le s).trans (Nat.mul_le_mul_left 400 (sq s (by omega)))
  have a7 := (hdRdCost_le W).trans (Nat.mul_le_mul_left 400 (sq W (by omega)))
  have b1 := (hdWrCost_le n).trans (Nat.mul_le_mul_left 2400 (sq n (by omega)))
  have b2 := (hdWrCost_le r).trans (Nat.mul_le_mul_left 2400 (sq r (by omega)))
  have b3 := (hdWrCost_le b).trans (Nat.mul_le_mul_left 2400 (sq b (by omega)))
  have b4 := (hdWrCost_le s).trans (Nat.mul_le_mul_left 2400 (sq s (by omega)))
  have b5 := (hdWrCost_le (W + 1)).trans (Nat.mul_le_mul_left 2400 (sq (W + 1) (by omega)))
  unfold hdrCost
  omega

/-- **The header extractor's budget** meets the per-entry bound. -/
theorem headerExtract_bound (B1 B2 : ℕ) : StageGreedyCollector.EntryBudgetBound (headerExtract B1 B2).1 := by
  obtain ⟨Kf, ef, hf⟩ := formatter_bound B1 B2
  obtain ⟨C, hC⟩ : ∃ C, C = sizingC B1 B2 := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = sizingE B1 B2 := ⟨_, rfl⟩
  refine ⟨100 * Kf + 200 + 30000 * (40 + 8 * C ^ 2) ^ 2, ef + 4 * E + 4, fun r => ?_⟩
  show 2 * hdrCostOf r + 2 ≤ _
  -- the formatted entry
  have hL := Control.output_length_le (formatter B1 B2) r
  have hfr := hf r
  simp only [frame_length] at hL
  -- the values
  have hsz := sizing_spec r
  rw [← hC, ← hE] at hsz
  have hW := hd_stackWidth_le r
  obtain ⟨hr, hb, hs⟩ := hd_selected_rbs_le r
  have hc := hd_clog_le_succ r.source.child.call.n
  have hcost := hdrCost_le r.termRequest.word.length r.source.child.call.n (hdX1 r)
    (hdX1 r + r.source.child.call.n + 6) r.source.child.selected.1.r r.source.child.selected.1.b
    r.source.child.selected.1.s r.termRequest.stackWidth
  change hdrCost _ _ _ _ _ _ _ _ ≤ _ at hcost
  have hx1 : hdX1 r ≤ (4 * r.source.child.call.n + 1) * (r.source.child.call.n + 1) + 5 := by
    unfold hdX1; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) 5
  unfold hdrCostOf
  generalize (EntryFormat.ofGreedy r).sizingMagnitude = z at hsz hW
  generalize r.termRequest.stackWidth = W at hW hcost ⊢
  generalize hdX1 r = x1 at hx1 hcost ⊢
  generalize r.termRequest.word.length = L at hL hcost ⊢
  generalize formatterBudget B1 B2 r = fb at hL hfr
  generalize r.source.child.selected.1.r = rr at hr hcost ⊢
  generalize r.source.child.selected.1.b = bb at hb hcost ⊢
  generalize r.source.child.selected.1.s = ss at hs hcost ⊢
  generalize r.source.child.selected.1.Uocc ^ (2 * r.degree) = U at hfr ⊢
  generalize r.source.child.call.n = n at *
  obtain ⟨X, hX⟩ : ∃ X, X = n + 1 := ⟨_, rfl⟩
  rw [← hX] at hfr hsz ⊢
  have hX1 : 1 ≤ X := by omega
  -- the values are polynomial
  have hzz : z ≤ z ^ 2 := Nat.le_self_pow (by norm_num) z
  have hz2 : z ^ 2 ≤ C ^ 2 * X ^ (2 * E) := by
    calc z ^ 2 ≤ (C * X ^ E) ^ 2 := Nat.pow_le_pow_left hsz 2
      _ = C ^ 2 * X ^ (2 * E) := by ring
  have hXX : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have hx1' : (4 * n + 1) * (n + 1) ≤ 4 * X ^ 2 := by rw [hX]; nlinarith
  have hp1 : X ^ 2 ≤ X ^ (2 * E + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hp2 : X ^ (2 * E) ≤ X ^ (2 * E + 2) := Nat.pow_le_pow_right hX1 (by omega)
  have hC2 : C ^ 2 * X ^ (2 * E) ≤ C ^ 2 * X ^ (2 * E + 2) := Nat.mul_le_mul_left _ hp2
  have hM : n + x1 + (x1 + n + 6) + rr + bb + ss + W + 2 ≤ (40 + 8 * C ^ 2) * X ^ (2 * E + 2) := by
    have e1 : (40 + 8 * C ^ 2) * X ^ (2 * E + 2) = 40 * X ^ (2 * E + 2) + 8 * (C ^ 2 * X ^ (2 * E + 2)) := by
      ring
    have hX2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
    omega
  have hM2 : (n + x1 + (x1 + n + 6) + rr + bb + ss + W + 2) ^ 2 ≤
      (40 + 8 * C ^ 2) ^ 2 * X ^ (4 * E + 4) := by
    calc _ ≤ ((40 + 8 * C ^ 2) * X ^ (2 * E + 2)) ^ 2 := Nat.pow_le_pow_left hM 2
      _ = _ := by ring
  -- collect
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (40 + 8 * C ^ 2) ^ 2 := ⟨_, rfl⟩
  rw [← hQ] at hM2 ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = X ^ (ef + 4 * E + 4) := ⟨_, rfl⟩
  have hPa : X ^ ef ≤ P := hP ▸ Nat.pow_le_pow_right hX1 (by omega)
  have hPb : X ^ (4 * E + 4) ≤ P := hP ▸ Nat.pow_le_pow_right hX1 (by omega)
  have hP1 : 1 ≤ P := hP ▸ Nat.one_le_pow _ _ hX1
  rw [← hP]
  have f1 : Kf * X ^ ef * (U + 1) ≤ Kf * P * (U + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hPa)
  have f2 : Q * X ^ (4 * E + 4) ≤ Q * P * (U + 1) :=
    (Nat.mul_le_mul_left _ hPb).trans (Nat.le_mul_of_pos_right _ (by omega))
  have f3 : 1 ≤ P * (U + 1) := le_trans hP1 (Nat.le_mul_of_pos_right P (Nat.succ_pos U))
  have hK : (100 * Kf + 200 + 30000 * Q) * P * (U + 1) =
      100 * (Kf * P * (U + 1)) + 200 * (P * (U + 1)) + 30000 * (Q * P * (U + 1)) := by ring
  rw [hK]
  have g1 : 14800 * (n + x1 + (x1 + n + 6) + rr + bb + ss + W + 2) ^ 2 ≤ 14800 * (Q * X ^ (4 * E + 4)) :=
    Nat.mul_le_mul_left _ hM2
  omega

end NearQuarticWires.StageGreedyEntry
