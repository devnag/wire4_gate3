import Proof.Quartic.StageNativeHeader.EmitRun

/-!
# The emission, phase by phase

Paper: `lem:print`, paper/paper.tex.

`emitCore_exec`: from a state whose input stream is at the marked cut bytes, whose column stream holds the marked
column content, whose accumulator and number streams are empty, with `d`, `p`, `G` in their registers and the working
registers at `0`, `emitP` leaves on the accumulator, head at `0`, the pieces of the marked native table request
(`EmitCost.marks_table_word`), changing only the registers of `emT`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairRepresentation (natWord)
open NearQuarticWires.Control

theorem s_ne {a b : Fin (hns + 1)} (h : a.val ≠ b.val) : a ≠ b := sne h

theorem sZp_ne_sZd : sZp ≠ sZd := sne (by simp [sZp, sZd, strm])
theorem sZG_ne_sZd : sZG ≠ sZd := sne (by simp [sZG, sZd, strm])
theorem sZG_ne_sZp : sZG ≠ sZp := sne (by simp [sZG, sZp, strm])
theorem sY_ne_sZd : sY ≠ sZd := sne (by simp [sY, sZd, strm])
theorem sY_ne_sZp : sY ≠ sZp := sne (by simp [sY, sZp, strm])
theorem sY_ne_sZG : sY ≠ sZG := sne (by simp [sY, sZG, strm])
theorem sIN_ne_sZd : sIN ≠ sZd := sne (by simp [sIN, sZd, strm])
theorem sIN_ne_sZp : sIN ≠ sZp := sne (by simp [sIN, sZp, strm])
theorem sIN_ne_sZG : sIN ≠ sZG := sne (by simp [sIN, sZG, strm])
theorem sIN_ne_sY : sIN ≠ sY := sne (by simp [sIN, sY, strm])

/-- The working registers, `0` before the emission. -/
def zeroRegs : List (Fin hnr) := [5, 6, 7, 8, 9, 10, eOP, eSC, eOZd, eOZp, eOZG, rQ, rV, rK1, rU, rTmp, eK2, eK3]

/-- The pieces of the marked native table request. -/
def pieces (d p G U q : ℕ) (C s : List Bool) : List Bool :=
  (natWord d).flatMap deep3 ++ (natWord p).flatMap deep3 ++ (natWord G).flatMap deep3 ++ C.flatMap deep3 ++
    s.flatMap deep3 ++ tailA ++ unary2 q ++ ([true, false] ++ tailA) ++ unary2 (U * U) ++ [true, false] ++
    unary2 (q - 1) ++ tail7

theorem emit_deep3_len (w : List Bool) : (w.flatMap deep3).length = 8 * w.length := by
  induction w with
  | nil => simp
  | cons b w ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp [deep3]; ring

theorem emit_unary2_len (k : ℕ) : (unary2 k).length = 4 * k := by simp [unary2]; ring

theorem pieces_length (d p G U q : ℕ) (C s : List Bool) :
    (pieces d p G U q C s).length = outLen (natWord d).length (natWord p).length (natWord G).length C.length
      s.length U q := by
  unfold pieces outLen
  simp only [List.length_append, emit_deep3_len, emit_unary2_len]
  simp [tailA, tail7]; ring

/-- **The emission, phase by phase.** -/
theorem emitCore_exec (cap : ℕ) (σ : WState hns hnr) (d p G U q : ℕ) (C s fw : List Bool)
    (hin : σ.st sIN = marks fw ++ marks s ++ [false]) (hinh : σ.sh sIN = (marks fw).length)
    (hy : σ.st sY = marks C ++ [false]) (hyh : σ.sh sY = 0) (ha : σ.st sACC = []) (hah : σ.sh sACC = 0)
    (hzd : σ.st sZd = []) (hzdh : σ.sh sZd = 0) (hzp : σ.st sZp = []) (hzph : σ.sh sZp = 0)
    (hzg : σ.st sZG = []) (hzgh : σ.sh sZG = 0)
    (hD : σ.val rD = d) (hP : σ.val rP = p) (hG : σ.val rG = G) (hz : ∀ x ∈ zeroRegs, σ.val x = 0)
    (hU : U = 2 ^ d) (hq : q = d + 2 * p + 3) (hGU : G ≤ U)
    (hcap : outLen (natWord d).length (natWord p).length (natWord G).length C.length s.length U q + U * U + q + 100
      ≤ cap) :
    ∃ τ, WExec cap emitP σ τ (coreCost d p G C.length s.length U q) ∧ τ.st sACC = pieces d p G U q C s ∧
      τ.sh sACC = 0 ∧ ∀ x, x ∉ emT → τ.val x = σ.val x := by
  have hdU : d < U := hU ▸ Nat.lt_two_pow_self
  have hU1 : 1 ≤ U := hU ▸ Nat.one_le_two_pow
  have hUU : U ≤ U * U := Nat.le_mul_of_pos_left U hU1
  have hnd := emit_nbl_le d
  have hnp := emit_nbl_le p
  have hnG := emit_nbl_le G
  have hwd := emit_natWord_len d
  have hwp := emit_natWord_len p
  have hwG := emit_natWord_len G
  have hO : 8 * ((natWord d).length + (natWord p).length + (natWord G).length + C.length + s.length) + 4 * q +
      4 * (U * U) + 4 * (q - 1) + 30 =
      outLen (natWord d).length (natWord p).length (natWord G).length C.length s.length U q := rfl
  have A0 : AccAt σ [] := ⟨ha, by rw [hah]; rfl, by rw [hz eOP (by decide)]; rfl⟩
  -- d
  have v0d : σ.val (wRd 0) = d := hD
  obtain ⟨τ1, e1, m1, sc1⟩ := numPhase cap sZd sACC_ne_sZd.symm wRd (by decide) (by decide) σ hzd hzdh
    (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide))
    (hz _ (by decide)) (hz _ (by decide)) A0.ho (by rw [v0d]; omega) (by rw [v0d]; omega)
    (by rw [v0d, hz eOP (by decide)]; omega) (by rw [v0d, hz eSC (by decide)]; omega)
  rw [v0d] at m1 sc1
  have A1 := A0.next m1
  -- p
  have v0p : τ1.val (wRp 0) = p := by show τ1.val rP = p; rw [m1.val rP (by decide) (by decide), hP]
  have zr1 : ∀ x, x ∈ zeroRegs → x ∉ [wRd 7, eSC] → x ≠ eOP → τ1.val x = 0 := fun x h1 h2 h3 => by
    rw [m1.val x h2 h3]; exact hz x h1
  obtain ⟨τ2, e2, m2, sc2⟩ := numPhase cap sZp sACC_ne_sZp.symm wRp (by decide) (by decide) τ1
    (by rw [m1.st sZp (by simp [sZp_ne_sZd]) sACC_ne_sZp.symm, hzp])
    (by rw [m1.sh sZp (by simp [sZp_ne_sZd]) sACC_ne_sZp.symm, hzph])
    (zr1 _ (by decide) (by decide) (by decide)) (zr1 _ (by decide) (by decide) (by decide))
    (zr1 _ (by decide) (by decide) (by decide)) (zr1 _ (by decide) (by decide) (by decide))
    (zr1 _ (by decide) (by decide) (by decide)) (zr1 _ (by decide) (by decide) (by decide))
    (zr1 _ (by decide) (by decide) (by decide)) A1.ho (by rw [v0p]; omega) (by rw [v0p]; omega)
    (by rw [v0p, A1.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil]; omega)
    (by rw [v0p, sc1, hz eSC (by decide)]; omega)
  rw [v0p] at m2 sc2
  have A2 := A1.next m2
  -- G
  have v0G : τ2.val (wRG 0) = G := by
    show τ2.val rG = G; rw [m2.val rG (by decide) (by decide), m1.val rG (by decide) (by decide), hG]
  have zr2 : ∀ x, x ∈ zeroRegs → x ∉ [wRd 7, eSC] → x ∉ [wRp 7, eSC] → x ≠ eOP → τ2.val x = 0 :=
    fun x h1 h2 h2' h3 => by rw [m2.val x h2' h3]; exact zr1 x h1 h2 h3
  obtain ⟨τ3, e3, m3, sc3⟩ := numPhase cap sZG sACC_ne_sZG.symm wRG (by decide) (by decide) τ2
    (by rw [m2.st sZG (by simp [sZG_ne_sZp]) sACC_ne_sZG.symm, m1.st sZG (by simp [sZG_ne_sZd]) sACC_ne_sZG.symm,
      hzg])
    (by rw [m2.sh sZG (by simp [sZG_ne_sZp]) sACC_ne_sZG.symm, m1.sh sZG (by simp [sZG_ne_sZd]) sACC_ne_sZG.symm,
      hzgh])
    (zr2 _ (by decide) (by decide) (by decide) (by decide)) (zr2 _ (by decide) (by decide) (by decide) (by decide))
    (zr2 _ (by decide) (by decide) (by decide) (by decide)) (zr2 _ (by decide) (by decide) (by decide) (by decide))
    (zr2 _ (by decide) (by decide) (by decide) (by decide)) (zr2 _ (by decide) (by decide) (by decide) (by decide))
    (zr2 _ (by decide) (by decide) (by decide) (by decide)) A2.ho (by rw [v0G]; omega) (by rw [v0G]; omega)
    (by rw [v0G, A2.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append]; omega)
    (by rw [v0G, sc2, sc1, hz eSC (by decide)]; omega)
  rw [v0G] at m3 sc3
  have A3 := A2.next m3
  -- the column content
  have zr3 : ∀ x, x ∉ [wRd 7, eSC] → x ∉ [wRp 7, eSC] → x ∉ [wRG 7, eSC] → x ≠ eOP → τ3.val x = σ.val x :=
    fun x h1 h2 h3 h4 => by rw [m3.val x h3 h4, m2.val x h2 h4, m1.val x h1 h4]
  have y3 : τ3.st sY = σ.st sY ∧ τ3.sh sY = σ.sh sY := ⟨by
      rw [m3.st sY (by simp [sY_ne_sZG]) sACC_ne_sY.symm, m2.st sY (by simp [sY_ne_sZp]) sACC_ne_sY.symm,
        m1.st sY (by simp [sY_ne_sZd]) sACC_ne_sY.symm],
    by rw [m3.sh sY (by simp [sY_ne_sZG]) sACC_ne_sY.symm, m2.sh sY (by simp [sY_ne_sZp]) sACC_ne_sY.symm,
        m1.sh sY (by simp [sY_ne_sZd]) sACC_ne_sY.symm]⟩
  have i3 : τ3.st sIN = σ.st sIN ∧ τ3.sh sIN = σ.sh sIN := ⟨by
      rw [m3.st sIN (by simp [sIN_ne_sZG]) sACC_ne_sIN.symm, m2.st sIN (by simp [sIN_ne_sZp]) sACC_ne_sIN.symm,
        m1.st sIN (by simp [sIN_ne_sZd]) sACC_ne_sIN.symm],
    by rw [m3.sh sIN (by simp [sIN_ne_sZG]) sACC_ne_sIN.symm, m2.sh sIN (by simp [sIN_ne_sZp]) sACC_ne_sIN.symm,
        m1.sh sIN (by simp [sIN_ne_sZd]) sACC_ne_sIN.symm]⟩
  have hL3 : (([] ++ (natWord d).flatMap deep3) ++ (natWord p).flatMap deep3 ++ (natWord G).flatMap deep3).length =
      8 * ((natWord d).length + (natWord p).length + (natWord G).length) := by
    simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil]; ring
  obtain ⟨τ4, e4, m4, -, -, sc4⟩ := copyPhase cap sY sACC_ne_sY.symm C [] [false] rfl τ3
    (by rw [y3.1, hy]; simp) (by rw [y3.2, hyh]; rfl) A3.ho (by rw [A3.2.2, hL3]; omega)
    (by rw [sc3, sc2, sc1, hz eSC (by decide)]; omega)
  have A4 := A3.next m4
  -- the cut bytes
  obtain ⟨τ5, e5, m5, -, -, sc5⟩ := copyPhase cap sIN sACC_ne_sIN.symm s (marks fw) [false] rfl τ4
    (by rw [m4.st sIN (by simp [sIN_ne_sY]) sACC_ne_sIN.symm, i3.1, hin])
    (by rw [m4.sh sIN (by simp [sIN_ne_sY]) sACC_ne_sIN.symm, i3.2, hinh]) A4.ho
    (by rw [A4.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil]; omega)
    (by rw [sc4, sc3, sc2, sc1, hz eSC (by decide)]; omega)
  have A5 := A4.next m5
  -- tailA
  obtain ⟨τ6, e6, m6⟩ := listPhase cap tailA τ5 A5.ho
    (by rw [A5.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil]; simp [tailA]; omega)
  have A6 := A5.next m6
  have zr6 : ∀ x, x ∉ [wRd 7, eSC] → x ∉ [wRp 7, eSC] → x ∉ [wRG 7, eSC] → x ≠ eSC → x ≠ eOP →
      τ6.val x = σ.val x := fun x h1 h2 h3 h4 h5 => by
    rw [m6.val x (by simp) h5, m5.val x (by simp [h4]) h5, m4.val x (by simp [h4]) h5, zr3 x h1 h2 h3 h5]
  -- q
  obtain ⟨τ7, e7, m7, q7, v7⟩ := qPhase cap τ6 d p
    (by rw [zr6 rD (by decide) (by decide) (by decide) (by decide) (by decide), hD])
    (by rw [zr6 rP (by decide) (by decide) (by decide) (by decide) (by decide), hP])
    (by rw [zr6 rQ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz rQ (by decide))
    (by rw [zr6 rV (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz rV (by decide))
    (by rw [zr6 rTmp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz rTmp (by decide))
    (by omega)
  rw [← hq] at q7 v7
  have A7 := A6.next m7
  have LS : ∀ (l : List Bool), l.length = l.length := fun _ => rfl
  -- unary q
  obtain ⟨τ8, e8, m8, k8⟩ := unaryPhase cap rQ (by decide) q τ7 q7 A7.ho
    (by rw [A7.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil];
        simp [tailA]; omega) (by omega)
  have A8 := A7.next m8
  -- [true, false] ++ tailA
  obtain ⟨τ9, e9, m9⟩ := listPhase cap ([true, false] ++ tailA) τ8 A8.ho
    (by rw [A8.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil,
        emit_unary2_len]; simp [tailA]; omega)
  have A9 := A8.next m9
  have zr9 : ∀ x, x ∉ [wRd 7, eSC] → x ∉ [wRp 7, eSC] → x ∉ [wRG 7, eSC] → x ≠ eSC → x ∉ [rQ, rV] → x ≠ eOP →
      τ9.val x = σ.val x := fun x h1 h2 h3 h4 h5 h6 => by
    have hQ : x ≠ rQ := fun h => h5 (by simp [h])
    rw [m9.val x (by simp) h6, m8.val x (by simp [hQ]) h6, m7.val x h5 h6, zr6 x h1 h2 h3 h4 h6]
  -- U = 2^d
  obtain ⟨τ10, e10, m10, u10, t10⟩ := uPhase cap τ9 d
    (by rw [zr9 rD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hD])
    (by rw [zr9 rU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz rU (by decide))
    (by rw [zr9 rK1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz rK1 (by decide))
    (by rw [zr9 rTmp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz rTmp (by decide))
    (by rw [← hU]; omega) A9.ho
    (by rw [A9.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil,
        emit_unary2_len]; simp [tailA]; omega)
  rw [← hU] at u10
  have A10 := A9.next m10
  -- U² ones
  obtain ⟨τ11, e11, m11⟩ := sqPhase cap τ10 U u10
    (by rw [m10.val eK2 (by decide) (by decide), zr9 eK2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hz eK2 (by decide))
    (by rw [m10.val eK3 (by decide) (by decide), zr9 eK3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)]; exact hz eK3 (by decide))
    t10 A10.ho
    (by rw [A10.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil,
        emit_unary2_len]; simp [tailA]; omega) (by omega)
  have A11 := A10.next m11
  -- [true, false]
  obtain ⟨τ12, e12, m12⟩ := listPhase cap [true, false] τ11 A11.ho
    (by rw [A11.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil,
        emit_unary2_len]; simp [tailA]; omega)
  have A12 := A11.next m12
  -- q − 1
  have v12 : τ12.val rV = q := by
    rw [m12.val rV (by simp) (by decide), m11.val rV (by decide) (by decide), m10.val rV (by decide) (by decide),
      m9.val rV (by simp) (by decide), m8.val rV (by decide) (by decide), v7]
  have e13 := WExec.dec (cap := cap) rV τ12 (by rw [v12]; omega)
  have m13 := emitted_setv τ12 rV (τ12.val rV - 1) (by decide)
  have A13 := A12.next m13
  obtain ⟨τ14, e14, m14, -⟩ := unaryPhase cap rV (by decide) (q - 1) (τ12.setv rV (τ12.val rV - 1))
    (by simp [v12]) A13.ho
    (by rw [A13.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil,
        emit_unary2_len]; simp [tailA]; omega) (by omega)
  have A14 := A13.next m14
  -- the empty fields
  obtain ⟨τ15, e15, m15⟩ := listPhase cap tail7 τ14 A14.ho
    (by rw [A14.2.2]; simp only [List.length_append, emit_deep3_len, List.nil_append, List.length_nil, List.append_nil,
        emit_unary2_len]; simp [tailA, tail7]; omega)
  have A15 := A14.next m15
  have hP15 : [] ++ (natWord d).flatMap deep3 ++ (natWord p).flatMap deep3 ++ (natWord G).flatMap deep3 ++
      C.flatMap deep3 ++ s.flatMap deep3 ++ tailA ++ [] ++ unary2 q ++ ([true, false] ++ tailA) ++ [] ++
      unary2 (U * U) ++ [true, false] ++ [] ++ unary2 (q - 1) ++ tail7 = pieces d p G U q C s := by
    simp only [pieces, List.nil_append, List.append_nil]
  rw [hP15] at A15
  have hlen := pieces_length d p G U q C s
  -- rewind
  have e16 := wrewind_spec cap sACC eOP (pieces d p G U q C s).length τ15 A15.2.2 (by rw [A15.2.2, hlen]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 (WExec.seq e13
    (WExec.seq e14 (WExec.seq e15 e16))))))))))))))) ?_, ?_, ?_, ?_⟩
  · rw [v0d, v0p, v0G, hlen, hwd, hwp, hwG, ← hq]
    unfold coreCost
    simp only [tailA, tail7, List.length_append, List.length_cons, List.length_nil]
    omega
  · simp only [WState.seth_st, WState.setv_st]; exact A15.1
  · simp only [WState.seth_sh, Function.update_self, WState.setv_sh]; rw [A15.2.1]; simp
  · intro x hx
    have hxO : x ≠ eOP := fun h => hx (by simp [h, emT])
    have n1 : x ∉ [wRd 7, eSC] := fun h => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    have n2 : x ∉ [wRp 7, eSC] := fun h => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    have n3 : x ∉ [wRG 7, eSC] := fun h => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    have n4 : x ≠ eSC := fun h => hx (by rw [h]; decide)
    have n5 : x ∉ [rQ, rV] := fun h => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    have n6 : x ≠ rV := fun h => n5 (by rw [h]; decide)
    have n7 : x ∉ [eK2, eK3] := fun h => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    have n8 : x ∉ [rK1, rU] := fun h => hx (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
    simp only [WState.seth_val, WState.setv_val, Function.update_of_ne hxO]
    rw [m15.val x (by simp) hxO, m14.val x (by simp [n6]) hxO, WState.setv_val, Function.update_of_ne n6,
      m12.val x (by simp) hxO, m11.val x n7 hxO, m10.val x n8 hxO, zr9 x n1 n2 n3 n4 n5 hxO]

end NearQuarticWires.StageNativeHeader
