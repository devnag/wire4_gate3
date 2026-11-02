import Proof.Quartic.StageNativeHeader.Arith
import Proof.Quartic.StageGreedyEntry.Half
import Proof.Quartic.StageGreedyEntry.Copy
import Proof.Wire_3_5.PrimAsmParseNat
import Proof.Wire_3_5.PrimAsmWriteNat

/-!
# The width field `q + 1` from the five input scalars

Paper: `lem:print`, paper/paper.tex.

`pfxP X OUT` unframes the input `w = natWord n ++ natWord r ++ natWord b ++ natWord s ++ natWord p ++ z` onto `X`,
rewinds the input, reads the five scalars, computes the dense width `(n+1)/2`, `(r/2)·s`, the row dimension
`d = (n+1)/2 − (r/2)·s` and `d + 2p + 4`, and writes `marks (natWord (d + 2p + 4))` on `OUT` (`pfx_run`). Only `X`
and `OUT` change among the streams; the input is unchanged and rewound.
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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec stp addTo addTo_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Recovery.HTParts (adv adv_st_src adv_sh_src adv_st_dst adv_sh_dst adv_val_OP adv_val_SC
  adv_val_other adv_st_other adv_sh_other)
open NearQuarticWires.StageNativeHeader (hnr rN rR rB rS rP rW rM rD rQ rK1 rTmp halfMulP halfMul_exec subP sub_exec
  ROnly)

variable {ns : ℕ}

/-! ## Registers -/

/-- The input cell counter, the unframing counter, the scratch of `readNatM`, the output counter, the copy counter. -/
def cS0 : Fin hnr := 40
def cOX : Fin hnr := 41
def pf : Fin hnr := 42
def pc : Fin hnr := 43
def pp : Fin hnr := 44
def pt : Fin hnr := 45
def cOO : Fin hnr := 46
def cSC : Fin hnr := 47

/-- The registers of the write of `q + 1`: the value, the scratch `5–10`, the output counter. -/
def wQ : Fin 8 ↪ Fin hnr := ⟨![rQ, 5, 6, 7, 8, 9, 10, cOO], by decide⟩

/-- One plain read from `X`. -/
noncomputable def rdX (X : Fin (ns + 1)) (v : Fin hnr) : WM ns hnr := readNatM false X pf pc v pp pt

/-- **The prefix program.** -/
noncomputable def pfxP (X OUT : Fin (ns + 1)) : WM ns hnr :=
  .seq (StageGreedyEntry.unframeP 0 X cS0 cOX) (.seq (WM.rewind 0 cS0) (.seq (WM.rewind X cOX)
  (.seq (rdX X rN) (.seq (rdX X rR) (.seq (rdX X rB) (.seq (rdX X rS) (.seq (rdX X rP)
  (.seq (addTo rN rK1 rTmp) (.seq (.inc rK1) (.seq (StageGreedyEntry.halfP rK1 rW)
  (.seq halfMulP (.seq subP
  (.seq (addTo rD rQ rTmp) (.seq (addTo rP rQ rTmp) (.seq (addTo rP rQ rTmp)
  (.seq (.inc rQ) (.seq (.inc rQ) (.seq (.inc rQ) (.seq (.inc rQ)
  (writeNatM OUT wQ))))))))))))))))))))

/-- The cost of one read. -/
def rdCostP (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

theorem pfx_two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hx)
    rw [pow_succ]; omega

theorem pfx_nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2)
  omega

theorem pfx_rd_le (x : ℕ) : rdCostP x ≤ 400 * (x + 1) ^ 2 := by
  unfold rdCostP
  have h1 := pfx_two_pow_nbl_le x
  have h2 := pfx_nbl_le x
  have h3 : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (80 * x + 120) :=
    Nat.mul_le_mul (by omega) (by omega)
  nlinarith

/-- A plain read of `natWord x` from `X` into `v`, after the words `us`. -/
theorem rdX_spec (cap : ℕ) (X : Fin (ns + 1)) (v : Fin hnr) (h1 : pf ≠ v) (h2 : pc ≠ v) (h3 : pp ≠ v)
    (h4 : v ≠ pt) (x : ℕ) (us rest : List Bool) (σ : WState ns hnr) (hst : σ.st X = us ++ natWord x ++ rest)
    (hsh : σ.sh X = us.length) (hf : σ.val pf = 0) (hc : σ.val pc = 0) (hp : σ.val pp = 0) (ht : σ.val pt = 0)
    (hcap : σ.val v + 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (rdX X v) σ ((σ.seth X (us ++ natWord x).length).setv v (σ.val v + x)) (rdCostP x) := by
  have e := readNatM_spec cap false X pf pc v pp pt (by decide) h1 (by decide) (by decide) h2 (by decide)
    (by decide) h3 (by decide) h4 x us rest σ
    (by simpa [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hst) hsh hf hc hp ht hcap
  refine WExec.cast cap e ?_ (le_refl _)
  simp [stp]

/-- **The run of the prefix program.** -/
theorem pfx_run (cap : ℕ) (X OUT : Fin (ns + 1)) (hX0 : X ≠ 0) (_hO0 : OUT ≠ 0) (hXO : X ≠ OUT)
    (n r b s p : ℕ) (z : List Bool) (hev : r % 2 = 0) (σ : WState ns hnr)
    (hst0 : σ.st 0 = frame ([n, r, b, s, p].flatMap natWord ++ z)) (hsh0 : σ.sh 0 = 0)
    (hX : σ.st X = []) (hXh : σ.sh X = 0) (hO : σ.st OUT = []) (hOh : σ.sh OUT = 0) (hv : ∀ x, σ.val x = 0)
    (hcap : 10 * ([n, r, b, s, p].flatMap natWord ++ z).length + 20 * (n + r + b + s + p + r / 2 * s) + 200 ≤ cap) :
    ∃ τ, WExec cap (pfxP X OUT) σ τ
        (200 * (([n, r, b, s, p].flatMap natWord ++ z).length + 1) +
          10 ^ 5 * (n + r + b + s + p + r / 2 * s + 2) ^ 2) ∧
      τ.st OUT = marks (natWord ((n + 1) / 2 - r / 2 * s + 2 * p + 4)) ∧
      τ.sh OUT = (τ.st OUT).length ∧ τ.val cOO = (τ.st OUT).length ∧ τ.val cSC = 0 ∧
      ∀ i, i ≠ X → i ≠ OUT → τ.st i = σ.st i ∧ τ.sh i = σ.sh i := by
  set w := [n, r, b, s, p].flatMap natWord ++ z with hw
  have hX0' : (0 : Fin (ns + 1)) ≠ X := Ne.symm hX0
  -- unframe, rewind both
  have e1 := StageGreedyEntry.unframe_spec cap (src := 0) (dst := X) (OP := cOX) (SC := cS0) hX0' (by decide) w [] []
    σ (by rw [hst0]; simp) (by rw [hsh0]; rfl) (by rw [hXh, hX]; rfl) (by rw [hv]; omega) (by rw [hv]; omega)
  set σ1 := adv 0 X cOX cS0 σ w (2 * w.length + 1) with hσ1
  have e2 := wrewind_spec cap 0 cS0 (2 * w.length + 1) σ1 (by simp [hσ1, adv, appendO, hv, cS0, cOX])
    (by simp [hσ1, adv, appendO, hv, cS0, cOX]; omega)
  set σ2 := (σ1.setv cS0 0).seth 0 (σ1.sh 0 - (2 * w.length + 1)) with hσ2
  have e3 := wrewind_spec cap X cOX w.length σ2
    (by simp [hσ2, hσ1, adv, appendO, hv, cS0, cOX])
    (by simp [hσ2, hσ1, adv, appendO, hv, cS0, cOX]; omega)
  set σ3 := (σ2.setv cOX 0).seth X (σ2.sh X - w.length) with hσ3
  have g3X : σ3.st X = w := by simp [hσ3, hσ2, hσ1, adv, appendO, hX, Function.update_apply, hX0]
  have g3Xh : σ3.sh X = 0 := by simp [hσ3, hσ2, hσ1, adv, appendO, hXh, Function.update_apply, hX0, hX0']
  have g3o : ∀ i, i ≠ X → σ3.st i = σ.st i ∧ σ3.sh i = σ.sh i := by
    intro i hi
    constructor
    · simp [hσ3, hσ2, hσ1, adv, appendO, Function.update_apply, hi]
    · by_cases h0 : i = 0
      · subst h0; simp [hσ3, hσ2, hσ1, adv, appendO, Function.update_apply, hi, hsh0]
      · simp [hσ3, hσ2, hσ1, adv, appendO, Function.update_apply, hi, h0]
  have g3v : ∀ x, σ3.val x = 0 := by
    intro x
    by_cases h1 : x = cOX
    · subst h1; simp [hσ3]
    · by_cases h2 : x = cS0
      · subst h2; simp [hσ3, hσ2, Function.update_of_ne h1]
      · simp [hσ3, hσ2, hσ1, adv, appendO, Function.update_of_ne h1, Function.update_of_ne h2, hv]
  have hwX : w = natWord n ++ (natWord r ++ (natWord b ++ (natWord s ++ (natWord p ++ z)))) := by
    simp [hw, List.append_assoc]
  have pw : ∀ x, 2 ^ (natBitLength x + 1) ≤ 4 * x + 4 := by
    intro x; have := pfx_two_pow_nbl_le x; rw [pow_succ]; omega
  -- the five reads
  have e4 := rdX_spec cap X rN (by decide) (by decide) (by decide) (by decide) n []
    (natWord r ++ (natWord b ++ (natWord s ++ (natWord p ++ z)))) σ3 (by rw [g3X, hwX]; simp) (by rw [g3Xh]; rfl)
    (g3v _) (g3v _) (g3v _) (g3v _) (by rw [g3v]; have := pw n; omega)
  set σ4 := (σ3.seth X ([] ++ natWord n).length).setv rN (σ3.val rN + n) with hσ4
  have e5 := rdX_spec cap X rR (by decide) (by decide) (by decide) (by decide) r (natWord n)
    (natWord b ++ (natWord s ++ (natWord p ++ z))) σ4 (by simp [hσ4, g3X, hwX]) (by simp [hσ4])
    (by simp (config := { decide := true }) [hσ4, g3v]) (by simp (config := { decide := true }) [hσ4, g3v])
    (by simp (config := { decide := true }) [hσ4, g3v]) (by simp (config := { decide := true }) [hσ4, g3v])
    (by simp (config := { decide := true }) [hσ4, g3v]; have := pw r; omega)
  set σ5 := (σ4.seth X (natWord n ++ natWord r).length).setv rR (σ4.val rR + r) with hσ5
  have e6 := rdX_spec cap X rB (by decide) (by decide) (by decide) (by decide) b (natWord n ++ natWord r)
    (natWord s ++ (natWord p ++ z)) σ5 (by simp [hσ5, hσ4, g3X, hwX]) (by simp [hσ5])
    (by simp (config := { decide := true }) [hσ5, hσ4, g3v]) (by simp (config := { decide := true }) [hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ5, hσ4, g3v]) (by simp (config := { decide := true }) [hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ5, hσ4, g3v]; have := pw b; omega)
  set σ6 := (σ5.seth X (natWord n ++ natWord r ++ natWord b).length).setv rB (σ5.val rB + b) with hσ6
  have e7 := rdX_spec cap X rS (by decide) (by decide) (by decide) (by decide) s
    (natWord n ++ natWord r ++ natWord b) (natWord p ++ z) σ6 (by simp [hσ6, hσ5, hσ4, g3X, hwX]) (by simp [hσ6])
    (by simp (config := { decide := true }) [hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ6, hσ5, hσ4, g3v]; have := pw s; omega)
  set σ7 := (σ6.seth X (natWord n ++ natWord r ++ natWord b ++ natWord s).length).setv rS (σ6.val rS + s) with hσ7
  have e8 := rdX_spec cap X rP (by decide) (by decide) (by decide) (by decide) p
    (natWord n ++ natWord r ++ natWord b ++ natWord s) z σ7 (by simp [hσ7, hσ6, hσ5, hσ4, g3X, hwX]) (by simp [hσ7])
    (by simp (config := { decide := true }) [hσ7, hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ7, hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ7, hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ7, hσ6, hσ5, hσ4, g3v])
    (by simp (config := { decide := true }) [hσ7, hσ6, hσ5, hσ4, g3v]; have := pw p; omega)
  set σ8 := (σ7.seth X (natWord n ++ natWord r ++ natWord b ++ natWord s ++ natWord p).length).setv rP
    (σ7.val rP + p) with hσ8
  have g8v : ∀ x, x ≠ rN → x ≠ rR → x ≠ rB → x ≠ rS → x ≠ rP → σ8.val x = 0 := by
    intro x h1 h2 h3 h4 h5
    simp [hσ8, hσ7, hσ6, hσ5, hσ4, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, g3v]
  have g8N : σ8.val rN = n := by simp (config := { decide := true }) [hσ8, hσ7, hσ6, hσ5, hσ4, g3v]
  have g8R : σ8.val rR = r := by simp (config := { decide := true }) [hσ8, hσ7, hσ6, hσ5, hσ4, g3v]
  have g8S : σ8.val rS = s := by simp (config := { decide := true }) [hσ8, hσ7, hσ6, hσ5, hσ4, g3v]
  have g8P : σ8.val rP = p := by simp (config := { decide := true }) [hσ8, hσ7, hσ6, hσ5, hσ4, g3v]
  have g8o : ∀ i, i ≠ X → σ8.st i = σ.st i ∧ σ8.sh i = σ.sh i := by
    intro i hi
    have := g3o i hi
    constructor
    · simp [hσ8, hσ7, hσ6, hσ5, hσ4, this.1]
    · simp [hσ8, hσ7, hσ6, hσ5, hσ4, Function.update_apply, hi, this.2]
  -- the dense width (n+1)/2
  have e9 := addTo_spec cap rN rK1 rTmp (by decide) (by decide) (by decide) σ8 (g8v _ (by decide) (by decide)
    (by decide) (by decide) (by decide)) (by rw [g8N]; omega)
    (by rw [g8N, g8v rK1 (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  set σ9 := σ8.setv rK1 (σ8.val rK1 + σ8.val rN) with hσ9
  have e10 := WExec.inc (cap := cap) rK1 σ9 (by
    simp (config := { decide := true }) [hσ9, g8N, g8v rK1 (by decide) (by decide) (by decide) (by decide) (by decide)]
    omega)
  set σ10 := σ9.setv rK1 (σ9.val rK1 + 1) with hσ10
  have g10K : σ10.val rK1 = n + 1 := by
    simp (config := { decide := true }) [hσ10, hσ9, g8N, g8v rK1 (by decide) (by decide) (by decide) (by decide)
      (by decide)]
  have e11 := StageGreedyEntry.halfP_exec cap rK1 rW (by decide) (n + 1) 0 σ10 g10K
    (by simp (config := { decide := true }) [hσ10, hσ9, g8v rW (by decide) (by decide) (by decide) (by decide)
      (by decide)]) (by omega) (by omega)
  set σ11 := (σ10.setv rK1 0).setv rW (0 + (n + 1) / 2) with hσ11
  have g11v : ∀ x, x ≠ rN → x ≠ rR → x ≠ rB → x ≠ rS → x ≠ rP → x ≠ rW → σ11.val x = 0 := by
    intro x h1 h2 h3 h4 h5 h6
    by_cases hk : x = rK1
    · subst hk; simp [hσ11, Function.update_of_ne h6]
    · simp [hσ11, hσ10, hσ9, Function.update_of_ne h6, Function.update_of_ne hk, g8v x h1 h2 h3 h4 h5]
  have g11 : σ11.val rR = r ∧ σ11.val rS = s ∧ σ11.val rP = p ∧ σ11.val rW = (n + 1) / 2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true }) [hσ11, hσ10, hσ9, g8R, g8S, g8P]
  -- (r/2)·s
  obtain ⟨σ12, e12, ro12, g12M, g12K⟩ := halfMul_exec cap σ11 r s g11.1 hev g11.2.1
    (by simp (config := { decide := true }) [hσ11]) (g11v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (g11v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by omega)
  -- d = (n+1)/2 − (r/2)·s
  obtain ⟨σ13, e13, ro13, g13D, g13K⟩ := sub_exec cap σ12 ((n + 1) / 2) (r / 2 * s)
    (by rw [ro12.val rW (by decide), g11.2.2.2]) g12M
    (by rw [ro12.val rD (by decide), g11v _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    g12K (by rw [ro12.val rTmp (by decide), g11v _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]) (by omega)
  have g13v : ∀ x, x ∉ [rK1, rM, rD] → σ13.val x = σ11.val x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [ro13.val x (by simp [hx.1, hx.2.2]), ro12.val x (by simp [hx.1, hx.2.1])]
  set d := (n + 1) / 2 - r / 2 * s with hd
  have g13D' : σ13.val rD = d := g13D
  have g13P : σ13.val rP = p := by rw [g13v rP (by decide), g11.2.2.1]
  have g13z : ∀ x, x ∉ [rK1, rM, rD] → x ≠ rN → x ≠ rR → x ≠ rB → x ≠ rS → x ≠ rP → x ≠ rW → σ13.val x = 0 :=
    fun x hx h1 h2 h3 h4 h5 h6 => by rw [g13v x hx]; exact g11v x h1 h2 h3 h4 h5 h6
  -- q + 1 = d + 2p + 4
  have e14 := addTo_spec cap rD rQ rTmp (by decide) (by decide) (by decide) σ13
    (g13z rTmp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [g13D']; omega)
    (by rw [g13D', g13z rQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; omega)
  set σ14 := σ13.setv rQ (σ13.val rQ + σ13.val rD) with hσ14
  have g13Q : σ13.val rQ = 0 :=
    g13z rQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have g14Q : σ14.val rQ = d := by
    rw [hσ14]; simp only [WState.setv_val, Function.update_self]; rw [g13Q, g13D']; simp
  have e15 := addTo_spec cap rP rQ rTmp (by decide) (by decide) (by decide) σ14
    (by simp (config := { decide := true }) [hσ14, g13z rTmp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)])
    (by simp (config := { decide := true }) [hσ14, g13P]; omega) (by
      rw [g14Q]; simp (config := { decide := true }) [hσ14, g13P]; omega)
  set σ15 := σ14.setv rQ (σ14.val rQ + σ14.val rP) with hσ15
  have g14P : σ14.val rP = p := by simp (config := { decide := true }) [hσ14, g13P]
  have g15Q : σ15.val rQ = d + p := by
    rw [hσ15]; simp only [WState.setv_val, Function.update_self]; rw [g14Q, g14P]
  have e16 := addTo_spec cap rP rQ rTmp (by decide) (by decide) (by decide) σ15
    (by simp (config := { decide := true }) [hσ15, hσ14, g13z rTmp (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)])
    (by simp (config := { decide := true }) [hσ15, hσ14, g13P]; omega) (by
      rw [g15Q]; simp (config := { decide := true }) [hσ15, hσ14, g13P]; omega)
  set σ16 := σ15.setv rQ (σ15.val rQ + σ15.val rP) with hσ16
  have g15P : σ15.val rP = p := by simp (config := { decide := true }) [hσ15, g14P]
  have g16Q : σ16.val rQ = d + 2 * p := by
    rw [hσ16]; simp only [WState.setv_val, Function.update_self]; rw [g15Q, g15P]; ring
  have e17 := WExec.inc (cap := cap) rQ σ16 (by rw [g16Q]; omega)
  set σ17 := σ16.setv rQ (σ16.val rQ + 1) with hσ17
  have e18 := WExec.inc (cap := cap) rQ σ17 (by simp [hσ17, g16Q]; omega)
  set σ18 := σ17.setv rQ (σ17.val rQ + 1) with hσ18
  have e19 := WExec.inc (cap := cap) rQ σ18 (by simp [hσ18, hσ17, g16Q]; omega)
  set σ19 := σ18.setv rQ (σ18.val rQ + 1) with hσ19
  have e20 := WExec.inc (cap := cap) rQ σ19 (by simp [hσ19, hσ18, hσ17, g16Q]; omega)
  set σ20 := σ19.setv rQ (σ19.val rQ + 1) with hσ20
  have g20Q : σ20.val rQ = d + 2 * p + 4 := by simp [hσ20, hσ19, hσ18, hσ17, g16Q]
  have g20v : ∀ x, x ≠ rQ → σ20.val x = σ13.val x := by
    intro x hx
    simp [hσ20, hσ19, hσ18, hσ17, hσ16, hσ15, hσ14, Function.update_of_ne hx]
  have g20st : σ20.st = σ8.st := by
    simp only [hσ20, hσ19, hσ18, hσ17, hσ16, hσ15, hσ14, WState.setv]; rw [ro13.st, ro12.st]; rfl
  have g20sh : σ20.sh = σ8.sh := by
    simp only [hσ20, hσ19, hσ18, hσ17, hσ16, hσ15, hσ14, WState.setv]; rw [ro13.sh, ro12.sh]; rfl
  have g20O : σ20.st OUT = [] := by rw [g20st]; rw [(g8o OUT (Ne.symm hXO)).1, hO]
  have g20Oh : σ20.sh OUT = 0 := by rw [g20sh]; rw [(g8o OUT (Ne.symm hXO)).2, hOh]
  have z20 : ∀ x, x ∉ [rK1, rM, rD] → x ≠ rN → x ≠ rR → x ≠ rB → x ≠ rS → x ≠ rP → x ≠ rW → x ≠ rQ →
      σ20.val x = 0 := fun x hx h1 h2 h3 h4 h5 h6 h7 => by rw [g20v x h7]; exact g13z x hx h1 h2 h3 h4 h5 h6
  -- write q + 1
  have e21 := writeNatM_spec cap OUT wQ σ20
    (z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [g20Oh, g20O]; rfl)
    (by
      have h0 : σ20.val (wQ 0) = d + 2 * p + 4 := g20Q
      have h7 : σ20.val (wQ 7) = 0 :=
        z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rw [h0, h7]; have := pfx_nbl_le (d + 2 * p + 4); omega)
  have hv0 : σ20.val (wQ 0) = d + 2 * p + 4 := g20Q
  rw [hv0] at e21
  have hr2s : r / 2 * (18 * s + 9) = 18 * (r / 2 * s) + 9 * (r / 2) := by ring
  have hdle : d ≤ n := by rw [hd]; omega
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 (WExec.seq e13
    (WExec.seq e14 (WExec.seq e15 (WExec.seq e16 (WExec.seq e17 (WExec.seq e18 (WExec.seq e19 (WExec.seq e20
    e21)))))))))))))))))))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g8N, g13D', g14P, g15P, hr2s]
    have q1 := pfx_rd_le n
    have q2 := pfx_rd_le r
    have q3 := pfx_rd_le b
    have q4 := pfx_rd_le s
    have q5 := pfx_rd_le p
    have hwr : (natBitLength (d + 2 * p + 4) + 10) * (100 * (d + 2 * p + 4) + 200) ≤
        2400 * (d + 2 * p + 4 + 1) ^ 2 := by
      have := pfx_nbl_le (d + 2 * p + 4)
      have h3 : (natBitLength (d + 2 * p + 4) + 10) * (100 * (d + 2 * p + 4) + 200) ≤
          (d + 2 * p + 4 + 11) * (100 * (d + 2 * p + 4) + 200) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hfl : (frame w).length = 2 * w.length + 1 := frame_length w
    obtain ⟨S, hS⟩ : ∃ S, S = n + r + b + s + p + r / 2 * s := ⟨_, rfl⟩
    have sq : ∀ x, x + 1 ≤ S + 2 → (x + 1) ^ 2 ≤ (S + 2) ^ 2 := fun x h => Nat.pow_le_pow_left h 2
    have k1 := sq n (by omega)
    have k2 := sq r (by omega)
    have k3 := sq b (by omega)
    have k4 := sq s (by omega)
    have k5 := sq p (by omega)
    have k6 : (d + 2 * p + 4 + 1) ^ 2 ≤ 9 * (S + 2) ^ 2 := by
      calc (d + 2 * p + 4 + 1) ^ 2 ≤ (3 * (S + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 9 * (S + 2) ^ 2 := by ring
    have k7 : S + 2 ≤ (S + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [← hS]
    generalize (S + 2) ^ 2 = Q at k1 k2 k3 k4 k5 k6 k7 ⊢
    generalize rdCostP n = A1 at q1 ⊢
    generalize rdCostP r = A2 at q2 ⊢
    generalize rdCostP b = A3 at q3 ⊢
    generalize rdCostP s = A4 at q4 ⊢
    generalize rdCostP p = A5 at q5 ⊢
    generalize (natBitLength (d + 2 * p + 4) + 10) * (100 * (d + 2 * p + 4) + 200) = A6 at hwr ⊢
    generalize (n + 1) ^ 2 = B1 at q1 k1
    generalize (r + 1) ^ 2 = B2 at q2 k2
    generalize (b + 1) ^ 2 = B3 at q3 k3
    generalize (s + 1) ^ 2 = B4 at q4 k4
    generalize (p + 1) ^ 2 = B5 at q5 k5
    generalize (d + 2 * p + 4 + 1) ^ 2 = B6 at hwr k6
    generalize r / 2 * s = m at hS ⊢
    generalize w.length = L
    have hd1 : (n + 1) / 2 ≤ n + 1 := Nat.div_le_self _ _
    have hr1 : r / 2 ≤ r := Nat.div_le_self _ _
    clear * - q1 q2 q3 q4 q5 hwr k1 k2 k3 k4 k5 k6 k7 hS hdle hd1 hr1
    clear_value d
    generalize (n + 1) / 2 = H at hd1 ⊢
    generalize r / 2 = R2 at hr1 ⊢
    linarith
  · simp only [appendO_st, Function.update_self, g20O, List.nil_append]
  · simp [appendO, g20Oh, g20O]
  · simp (config := { decide := true }) [appendO, wQ, g20O]
    exact z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · simp (config := { decide := true }) [appendO, wQ]
    exact z20 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro i hi1 hi2
    have hst : (appendO σ20 OUT (wQ 7) (marks (natWord (d + 2 * p + 4)))).st i = σ20.st i := by
      simp [appendO, Function.update_of_ne hi2]
    have hsh : (appendO σ20 OUT (wQ 7) (marks (natWord (d + 2 * p + 4)))).sh i = σ20.sh i := by
      simp [appendO, Function.update_of_ne hi2]
    rw [hst, hsh, g20st, g20sh]
    exact g8o i hi1

end NearQuarticWires.StageCertNativeOutput
