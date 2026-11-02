import Proof.Quartic.StageCertNativeOutput.Compose
import Proof.Quartic.StageCertNativeOutput.Prefix
import Proof.Quartic.StagePrint.DenseWidth
import Proof.Gates.CounterAsm.Copy
import Proof.Quartic.Control.GammaControl

/-!
# The native output: the width field, then the published table stream

Paper: `lem:print` and `prop:time`, paper/paper.tex.

One program on the streams of `headerTableWF h` (its tape `j` is stream `j`, the input on stream `0`), a ruler, a
work stream `X` and the output stream `OUT`: the prefix `pfxP` writes `marks (natWord (q + 1))` on `OUT` from the five
input scalars (`q + 1 = (n+1)/2 − (r/2)·s + 2p + 4`, `q1_eq`), then `headerTableWF h` runs once on its bank (the
native header printer, then the published table call), then its output `frame (table.output)` is copied cell by cell
onto `OUT` (`out_run`). `OUT` ends holding `frame (natWord (q + 1) ++ table.output)`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

namespace NearQuarticWires.StageCertNativeOutput

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.Expand.PolyTab (idealStart wordFunction_of_ideal)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StageNativeHeader (hnr)
open StagePrint.Downstream

section Layout

variable (t : ℕ)

/-- Tape `j` of the composed call is stream `j`. -/
def oBank (j : Fin t) : Fin (t + 2 + 1) := ⟨j.val, by have := j.isLt; omega⟩

/-- The ruler of the call, the work stream, the output stream. -/
def oRuler : Fin (t + 2 + 1) := ⟨t, by omega⟩
def oX : Fin (t + 2 + 1) := ⟨t + 1, by omega⟩
def oOUT : Fin (t + 2 + 1) := ⟨t + 2, by omega⟩

theorem oBank_injective : Function.Injective (oBank t) := fun a b h =>
  Fin.ext (by simpa [oBank] using congrArg Fin.val h)

theorem oBank_ne_ruler (j : Fin t) : oBank t j ≠ oRuler t := fun h => by
  have := congrArg Fin.val h; simp [oBank, oRuler] at this; omega

theorem oBank_ne_X (j : Fin t) : oBank t j ≠ oX t := fun h => by
  have := congrArg Fin.val h; simp [oBank, oX] at this; omega

theorem oBank_ne_OUT (j : Fin t) : oBank t j ≠ oOUT t := fun h => by
  have := congrArg Fin.val h; simp [oBank, oOUT] at this; omega

theorem oX_ne_zero : oX t ≠ 0 := fun h => by have := congrArg Fin.val h; simp [oX] at this
theorem oOUT_ne_zero : oOUT t ≠ 0 := fun h => by have := congrArg Fin.val h; simp [oOUT] at this
theorem oX_ne_OUT : oX t ≠ oOUT t := fun h => by have := congrArg Fin.val h; simp [oX, oOUT] at this

/-- The rulers: the call's budget on its ruler, every other stream empty. -/
def oLens (bud : ℕ) (i : Fin (t + 2 + 1)) : ℕ := if i.val = t then bud else 0

/-- **The output program.** -/
noncomputable def outP {s : ℕ} (M : Machine t s) (o : Fin t) : WMX (t + 2) hnr :=
  .seq (.wm (pfxP (oX t) (oOUT t))) (.seq (WMX.machZ M (oBank t) (oRuler t))
    (.wm (frameCopy (oBank t o) cSC (fun b => emitC (oOUT t) cOO b))))

end Layout

/-! ## The width field -/

/-- **`q + 1` from the five scalars.** -/
theorem q1_eq (r : NativeHeaderRequest) :
    (r.parameters.n + 1) / 2 - r.parameters.r / 2 * r.parameters.s + 2 * r.table.matrix.p + 4 = r.table.q + 1 := by
  have h1 := (StageNativeHeader.dRow_eq r.parameters).1
  have h2 := StagePrint.native_width_eq_half r.parameters
  have h3 : r.table.q = r.table.matrix.d + 2 * r.table.matrix.p + 3 := rfl
  rw [h3, r.dimension_eq, h1, h2]

theorem marks_frame_append (a b : List Bool) : marks a ++ frame b = frame (a ++ b) := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks, NearCubicGates.Close.Codec.frame_eq_marks,
    Streaming.marks_append, List.append_assoc]

theorem flatMap_single' : ∀ w : List Bool, (w.flatMap fun b => [b]) = w
  | [] => rfl
  | b :: w => by simp only [List.flatMap_cons]; rw [flatMap_single' w]; rfl

/-- The cost of the prefix on one request. -/
def pfxCostOf (r : NativeHeaderRequest) : ℕ :=
  200 * (r.word.length + 1) + 10 ^ 5 * (r.parameters.n + r.parameters.r + r.parameters.b + r.parameters.s +
    r.table.matrix.p + r.parameters.r / 2 * r.parameters.s + 2) ^ 2

/-- The register capacity on one request. -/
def outCap (bF : ℕ) (r : NativeHeaderRequest) : ℕ :=
  10 * r.word.length + 20 * (r.parameters.n + r.parameters.r + r.parameters.b + r.parameters.s +
    r.table.matrix.p + r.parameters.r / 2 * r.parameters.s) + 200 + 4 * (r.table.q + 1) + 10 + 2 * (bF + 2)

/-- **The run of the output program**, for any word function from the request to `frame (table.output)`. -/
theorem out_run {bF : NativeHeaderRequest → ℕ}
    (F : WordFunction NativeHeaderRequest NativeHeaderRequest.word (fun r => frame r.table.output) bF)
    (r : NativeHeaderRequest) :
    ∃ τ, WXExec (outCap (bF r) r) (outP F.program.tapeCount F.program.machine F.program.outputTape)
        (idealStart (F.program.tapeCount + 2) hnr r.word (oLens F.program.tapeCount (bF r))) τ
        (pfxCostOf r + 1 + (2 * bF r + 2 + 1 + (frame r.table.output).length * (2 * 7 + 25))) ∧
      τ.st (oOUT F.program.tapeCount) = frame (natWord (r.table.q + 1) ++ r.table.output) := by
  set t := F.program.tapeCount with ht
  set cap := outCap (bF r) r with hcapd
  set σ0 := idealStart (t + 2) hnr r.word (oLens t (bF r)) with hσ0
  have hst0 : ∀ i : Fin (t + 2 + 1), σ0.st i =
      if i.val = 0 then frame r.word else List.replicate (oLens t (bF r) i) false := fun i => rfl
  have hsh0 : ∀ i : Fin (t + 2 + 1), σ0.sh i = 0 := fun i => rfl
  have hev : r.parameters.r % 2 = 0 := Nat.even_iff.mp r.parameters.r_even
  have hOL : ∀ i : Fin (t + 2 + 1), i.val ≠ t → oLens t (bF r) i = 0 := fun i h => by simp [oLens, h]
  have h2t := F.program.twoTapes
  -- the prefix
  obtain ⟨τ1, e1, g1O, g1Oh, g1OO, g1SC, g1o⟩ := pfx_run cap (oX t) (oOUT t) (oX_ne_zero t) (oOUT_ne_zero t)
    (oX_ne_OUT t) r.parameters.n r.parameters.r r.parameters.b r.parameters.s r.table.matrix.p r.stream hev σ0
    (by rw [hst0]; rfl) (hsh0 _)
    (by rw [hst0, if_neg (by simp [oX]), hOL _ (by simp [oX])]; rfl) (hsh0 _)
    (by rw [hst0, if_neg (by simp [oOUT]), hOL _ (by simp [oOUT])]; rfl) (hsh0 _) (fun _ => rfl)
    (by
      have hw : r.word = [r.parameters.n, r.parameters.r, r.parameters.b, r.parameters.s,
        r.table.matrix.p].flatMap natWord ++ r.stream := rfl
      simp only [hcapd, outCap, ← hw]; omega)
  rw [q1_eq] at g1O
  -- the call
  obtain ⟨rf, hrf, hof⟩ := F.realizes r
  have hin : (fun j => τ1.st (oBank t j)) = F.program.inputTapes r.word := by
    funext j
    rw [(g1o _ (oBank_ne_X t j) (oBank_ne_OUT t j)).1, hst0]
    unfold Program.inputTapes
    have hv : (oBank t j).val = j.val := rfl
    by_cases hj : j.val = 0
    · rw [if_pos (by rw [hv]; exact hj), if_pos hj]
    · rw [if_neg (by rw [hv]; exact hj), if_neg hj, hOL _ (by rw [hv]; have := j.isLt; omega)]; rfl
  have hrun : LocalBitMultitape.run F.program.machine (bF r) (fun j => τ1.st (oBank t j)) = some rf := by
    rw [hin]; exact hrf
  obtain ⟨τ2, e2, d2⟩ := WXExec.machZ_run cap (oBank_injective t) (oBank_ne_ruler t) τ1 hrun
    (fun j => by rw [(g1o _ (oBank_ne_X t j) (oBank_ne_OUT t j)).2, hsh0])
    (by
      have hRX : oRuler t ≠ oX t := fun h => by have := congrArg Fin.val h; simp [oRuler, oX] at this
      have hRO : oRuler t ≠ oOUT t := fun h => by have := congrArg Fin.val h; simp [oRuler, oOUT] at this
      rw [(g1o _ hRX hRO).1, hst0, if_neg (by simp [oRuler]; omega)]
      simp [oLens, oRuler])
    (by
      have hRX : oRuler t ≠ oX t := fun h => by have := congrArg Fin.val h; simp [oRuler, oX] at this
      have hRO : oRuler t ≠ oOUT t := fun h => by have := congrArg Fin.val h; simp [oRuler, oOUT] at this
      rw [(g1o _ hRX hRO).2, hsh0]) le_rfl
  have hOUTfar : ∀ j, oBank t j ≠ oOUT t := oBank_ne_OUT t
  have g2O := d2.other (oOUT t) hOUTfar
  -- the copy
  have hfl : (frame r.table.output).length = 2 * r.table.output.length + 1 := frame_length _
  have e3 := frameCopy_spec cap (src := oBank t F.program.outputTape) (dst := oOUT t) (OP := cOO) (SC := cSC)
    (oBank_ne_OUT t _) (by decide) (d := 1) (emits_raw cap) (fun _ => le_refl _) r.table.output [] [] τ2
    (by rw [d2.st, hof]; simp) (d2.sh _) (by rw [g2O.1, g2O.2]; exact g1Oh)
    (by rw [d2.val, g1OO, g1O, Streaming.marks_length]
        have hq := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length (r.table.q + 1)
        have hb := pfx_nbl_le (r.table.q + 1)
        have hL := Control.output_length_le F r
        simp only [hcapd, outCap]; omega)
    (by rw [d2.val, g1SC]; have hL := Control.output_length_le F r; simp only [hcapd, outCap]; omega)
  refine ⟨_, WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.wm e3)), ?_⟩
  rw [adv_st_dst, g2O.1, g1O, flatMap_single', marks_frame_append]

/-! ## The budget -/

/-- `r`, `b`, `s` of the partition are at most `n + 1`. -/
theorem params_le (P : StarParams) : P.r ≤ P.n ∧ P.b ≤ P.n ∧ P.s ≤ P.n + 1 := by
  have h4 := P.four_r_le_n
  have h2 := P.two_le_r
  have hpow : 2 ^ P.s ≤ P.n / P.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have hdiv : P.n / P.r ≤ P.n := Nat.div_le_self _ _
  have hslt : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  have hb : P.b = 2 ^ P.s - 1 := rfl
  omega

/-- **The cost of the output program is within the frozen budget.** -/
theorem out_budget_le (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeHeaderRequest) :
    2 * (pfxCostOf r + 1 + (2 * htBudget h r + 2 + 1 + (frame r.table.output).length * (2 * 7 + 25))) + 2 ≤
      StageCertNative.Output.budget h r := by
  have hL := Control.output_length_le (headerTableWF h) r
  obtain ⟨hr, hb, hs⟩ := params_le r.parameters
  have hrs : r.parameters.r / 2 * r.parameters.s ≤ r.parameters.n * (r.parameters.n + 1) :=
    Nat.mul_le_mul ((Nat.div_le_self _ _).trans hr) hs
  have hst : r.stream.length ≤ r.word.length := by
    have : r.word = [r.parameters.n, r.parameters.r, r.parameters.b, r.parameters.s,
      r.table.matrix.p].flatMap natWord ++ r.stream := rfl
    rw [this, List.length_append]; omega
  unfold StageCertNative.Output.budget pfxCostOf
  unfold htBudget headerBudget tableBudget at hL ⊢
  generalize StageRecovery.NativeTableFrame.steps (StageRecovery.NativeTableFrame.publishedAlgorithm h) r.table = T
    at hL ⊢
  generalize (frame r.table.output).length = O at hL ⊢
  generalize r.parameters.r / 2 * r.parameters.s = m at hrs ⊢
  generalize r.word.length = W at hst ⊢
  generalize r.stream.length = Z at hst hL ⊢
  generalize r.table.count = C at hL ⊢
  generalize r.parameters.r = rr at hr hrs ⊢
  generalize r.parameters.b = bb at hb ⊢
  generalize r.parameters.s = ss at hs hrs ⊢
  generalize r.table.matrix.p = p at hL ⊢
  generalize r.parameters.n = n at hr hb hs hrs hL ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = n + p + 2 := ⟨_, rfl⟩
  rw [← hX] at hL ⊢
  obtain ⟨Y, hY⟩ : ∃ Y, Y = W + C + T + 1 := ⟨_, rfl⟩
  rw [← hY]
  have hX1 : 1 ≤ X := by omega
  have hsq : (n + rr + bb + ss + p + m + 2) ^ 2 ≤ 36 * X ^ 4 := by
    have h1 : n + rr + bb + ss + p + m + 2 ≤ 6 * X ^ 2 := by
      have : n * (n + 1) ≤ X ^ 2 := by rw [hX]; nlinarith
      have : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
      omega
    calc _ ≤ (6 * X ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = 36 * X ^ 4 := by ring
  have hx4 : X ^ 4 ≤ X ^ 20 := Nat.pow_le_pow_right hX1 (by norm_num)
  have hx20 : X ^ 20 ≤ X ^ 60 := Nat.pow_le_pow_right hX1 (by norm_num)
  have hY1 : 1 ≤ Y := by omega
  have hZ : Z + C + 1 ≤ Y := by omega
  have a1 : 10 ^ 30 * X ^ 20 * (Z + C + 1) ≤ 10 ^ 30 * (X ^ 20 * Y) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZ)
  have a2 : X ^ 4 ≤ X ^ 20 * Y := hx4.trans (Nat.le_mul_of_pos_right _ hY1)
  have a3 : Y ≤ X ^ 20 * Y := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hX1)
  have a4 : X ^ 20 * Y ≤ X ^ 60 * Y := Nat.mul_le_mul_right _ hx20
  have e5 : 10 ^ 50 * X ^ 60 * Y = 10 ^ 50 * (X ^ 60 * Y) := by ring
  rw [e5]
  generalize (n + rr + bb + ss + p + m + 2) ^ 2 = Q at hsq ⊢
  generalize X ^ 4 = X4 at hsq a2
  generalize X ^ 20 * Y = A at a1 a2 a3 a4
  generalize X ^ 60 * Y = B at a4 ⊢
  generalize 10 ^ 30 * X ^ 20 * (Z + C + 1) = H at a1 hL ⊢
  clear * - hL hst hsq a1 a2 a3 a4 hY hY1
  linarith

/-- **The native output producer**: the width field `q + 1` computed from the five scalars, then the native header
printer and the published table call, once each, then the table stream, all in one frame. -/
noncomputable def nativeOutputWordFunction (h : Bindings.Williams14.Williams14_Corollary4_4) :
    StageCertNative.Output.Producer h :=
  wordFunction_of_ideal
    (outP (headerTableWF h).program.tapeCount (headerTableWF h).program.machine (headerTableWF h).program.outputTape)
    (oOUT _) (by simp [oOUT]) (fun r => outCap (htBudget h r) r)
    (fun r => oLens (headerTableWF h).program.tapeCount (htBudget h r))
    (fun r => pfxCostOf r + 1 + (2 * htBudget h r + 2 + 1 + (frame r.table.output).length * (2 * 7 + 25)))
    (out_budget_le h) (fun r => ⟨by simp [oLens, oOUT], out_run (headerTableWF h) r⟩)

end NearQuarticWires.StageCertNativeOutput
