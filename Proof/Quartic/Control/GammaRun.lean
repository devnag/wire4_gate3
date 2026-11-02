import Proof.Quartic.Control.GammaHead

/-!
# The coefficient stage: the whole program

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `cor:conditional`; `prop:time`. After the phase before the walks (`gammaHead_exec`), the program runs all the walks (`Control.walks_exec`,
whose states are described up to reading), brings the table head back behind its two zero cells
(`sentinelRewind_exec`) and appends the framed table to the child input already on the output (`tableTail_exec`).
The output stream is never touched by the walks (`walksP_avoids`), so the output word is exact (`gammaP_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicGates.Close.Interfaces (Call)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (SimW RdEq)

/-- Two registers of the prelude differ (by their indices). -/
local macro "pdst" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cG, cOP, cC, cLC, cD, cNX, rS, rO, rI, rH,
    rT] at hv <;> omega))

/-- The last phase: the framed table after the child input. -/
def tailP (t : ℕ) : WMX (cns t) lnr :=
  .seq (copyLoop true (cT t) (cOUT t) rO rI)
    (.seq (.wm (NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair (cOUT t) rO false)) (.wm (emitC (cOUT t) rO false)))

/-- **The coefficient-stage program** for the coefficient program `p`. -/
noncomputable def gammaP (p : Program) : WMX (cns p.tapeCount) lnr :=
  .seq (headP p.tapeCount) (.seq (walksP p) (.seq (.wm (sentinelRewind (cT _))) (tailP _)))

theorem rdEq_append_false (l : List Bool) : RdEq (l ++ [false]) l := by
  intro q
  unfold readTapeBit
  rcases Nat.lt_or_ge q l.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_default l false h, List.getD_append_right _ _ _ _ h]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'; simp
    · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem tableMarks_eq (γ : ℕ → ℤ) (n : ℕ) :
    tableMarks γ n = marks ((List.range n).flatMap fun i => NearCubicGates.Close.Interfaces.intWord (γ i)) := by
  rw [tableMarks, NearCubicGates.Close.Codec.marks_flatMap]

/-- The table word appended by the program: the number of walks, then the coefficients. -/
def tableWord (kh : ℕ) (γ : ℕ → ℤ) : List Bool :=
  natWord (2 ^ (8 * kh)) ++ (List.range (2 ^ (8 * kh))).flatMap fun i => NearCubicGates.Close.Interfaces.intWord (γ i)

/-- The cost of the coefficient-stage program. -/
def gammaCost (c : Call) (xs ys zs ps ws fs : List ℕ) (k Q ell : ℕ) (wp cb π w : List Bool) (Win B U : ℕ) : ℕ :=
  headCost c xs ys zs ps ws fs k Q ell wp cb π w + 1 + (2 ^ (k / 2 * 8) *
    (walkCost (headWord ell (k / 2) Q π).length (k / 2) (16 * (k / 2) + 8) Win B + 7) + 1 + 1 +
    (5 * U + 9 + 1 + (U * 52 + 1 + 1 + (15 + 1 + 7))))

/-- **The coefficient stage.** From the start on the child input `w`, with a coefficient word function `f` whose
request `req i` for the walk of index `i` has the input `headWord ++ natWord 8 ++ natWords (digits of i)`, the
program writes exactly `frame (w ++ frame (tableWord kh γ))` on the output, `γ i` the value of `req i`. -/
theorem gammaP_exec {Request : Type} {input : Request → List Bool} {Rv : Request → ℤ} {budget : Request → ℕ}
    (f : WordFunction Request input (fun r => NearCubicGates.Close.Interfaces.intWord (Rv r)) budget)
    (cap : ℕ) (w : List Bool) (c : Call) (xs ys zs ps ws fs : List ℕ) (k Q ell : ℕ) (wp cb π : List Bool)
    (hw : w = seedPre c xs k ys Q ell ++ (tailWord zs ps ws fs wp cb ++ frame π))
    (hxs : xs.length = 6) (hys : ys.length = 10) (hzs : zs.length = 18) (hws : ws.length = 9)
    (hfit : ReadFits cap c xs k) (hyfit : ∀ y ∈ ys, natBitLength y + 1 ≤ cap)
    (hzf : ∀ x ∈ zs, natBitLength x + 1 ≤ cap) (hwf : ∀ x ∈ ws, natBitLength x + 1 ≤ cap)
    (hpf : ListFits cap ps) (hff : ListFits cap fs)
    (hcapW : 6 * w.length + 6 ≤ cap)
    (hcapS : 4 * (seedWord ell (k / 2) Q).length + k + 6 * natBitLength k + 20 ≤ cap)
    (hcapP : 2 * (seedWord ell (k / 2) Q).length + 12 * π.length + 30 ≤ cap)
    (hcapT : 2 * (headWord ell (k / 2) Q π).length + 40 * (k / 2) + 20 + 16 * (k / 2) + 8 ≤ cap)
    (req : ℕ → Request)
    (hin : ∀ i, input (req i) = headWord ell (k / 2) Q π ++ natWord 8 ++ (walkDigits (k / 2) 8 i).flatMap natWord)
    (B Win : ℕ) (hB : ∀ i, budget (req i) ≤ B) (hWin : ∀ i, (input (req i)).length ≤ Win)
    (hcapK : 10 * ((headWord ell (k / 2) Q π).length + 8 * (k / 2) + (16 * (k / 2) + 8) + B + 50) + 8 * 8 +
      10 * (8 + 2) * (4 * (k / 2) + 8) ≤ cap)
    (hcapU : 6 * w.length + 6 * (tableWord (k / 2) fun i => Rv (req i)).length + 20 ≤ cap) :
    ∃ τ, WXExec cap (gammaP f.program) (gammaStart _ w) τ
      (gammaCost c xs ys zs ps ws fs k Q ell wp cb π w Win B (tableWord (k / 2) fun i => Rv (req i)).length) ∧
      τ.st (cOUT _) = frame (w ++ frame (tableWord (k / 2) fun i => Rv (req i))) := by
  set t := f.program.tapeCount with ht
  set kh := k / 2 with hkh
  obtain ⟨τ5, E5, HD⟩ := gammaHead_exec cap t w c xs ys zs ps ws fs k Q ell wp cb π hw hxs hys hzs hws hfit hyfit
    hzf hwf hpf hff hcapW hcapS hcapP hcapT
  set hw' := headWord ell kh Q π with hhw'
  set Tw := startTable Q kh π with hTw
  have hLH : cL t ≠ cHS t := cne _ (by simp [cL, cHS])
  have hTAH : cTA t ≠ cHS t := cne _ (by simp [cTA, cHS])
  have hGAH : cGA t ≠ cHS t := cne _ (by simp [cGA, cHS])
  have hCH : cCT t ≠ cHS t := cne _ (by simp [cCT, cHS])
  have hTH : cT t ≠ cHS t := cne _ (by simp [cT, cHS])
  have hOH : cOUT t ≠ cHS t := cne _ (by simp [cOUT, cHS])
  have hTC : cT t ≠ cCT t := cne _ (by simp [cT, cCT])
  have hTO : cT t ≠ cOUT t := cne _ (by simp [cT, cOUT])
  have hbH : ∀ j, cbank t j ≠ cHS t := fun j => cne _ (by simp [cbank, cHS]; omega)
  set ρ := (τ5.sets (cHS t) (marks hw' ++ [false])).setv cNX 0 with hρ
  have hv : ∀ r, r ≠ cNX → ρ.val r = τ5.val r := fun r hr => by simp [hρ, Function.update_of_ne hr]
  have hready : CoeffReady t ρ hw' kh (16 * kh + 8) := {
    hs := by simp [hρ]
    hsh := by simp [hρ, HD.hsh]
    cth := by simp [hρ, HD.cth]
    ruler := by simp [hρ, Function.update_of_ne hLH, HD.ruler]
    rulerh := by simp [hρ, HD.rulerh]
    b := fun j => by simp [hρ, Function.update_of_ne (hbH j), HD.b]
    bh := fun j => by simp [hρ, HD.bh]
    ta := by simp [hρ, Function.update_of_ne hTAH, HD.ta]
    tah := by simp [hρ, HD.tah]
    ga := by simp [hρ, Function.update_of_ne hGAH, HD.ga]
    gah := by simp [hρ, HD.gah]
    rs := fun i => by rw [hv _ (by pdst)]; exact HD.rs i
    op := by rw [hv _ (by pdst)]; exact HD.op
    c := by rw [hv _ (by pdst)]; exact HD.c
    d := by rw [hv _ (by pdst)]; exact HD.d
    lc := by rw [hv _ (by pdst)]; exact HD.lc
    y := fun i => by rw [hv _ (by pdst)]; exact HD.y i
    r := fun i => by rw [hv _ (by pdst)]; exact HD.r i
    z0 := by rw [hv _ (by pdst)]; exact HD.z0
    z1 := by rw [hv _ (by pdst)]; exact HD.z1
    z2 := by rw [hv _ (by pdst)]; exact HD.z2
    z3 := by rw [hv _ (by pdst)]; exact HD.z3
    z4 := by rw [hv _ (by pdst)]; exact HD.z4 }
  have hσ : SimW (coeffSt (ρ.setv cNX 1) kh (walkDigits kh 8 0) Tw) τ5 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext q
      by_cases hq : q = cT t
      · subst hq; simp [coeffSt, HD.tth]
      · simp [coeffSt, hρ, Function.update_of_ne hq]
    · funext r
      by_cases hr : r = cNX
      · subst hr; simp [coeffSt, HD.nx]
      · simp [coeffSt, hρ, Function.update_of_ne hr]
    · simp [coeffSt, hρ]
    · intro i
      by_cases hiT : i = cT t
      · subst hiT; simp [coeffSt, HD.tt]; exact RdEq.refl _
      · by_cases hiC : i = cCT t
        · subst hiC; simp [coeffSt, Function.update_of_ne hTC.symm, HD.ct]; exact RdEq.refl _
        · by_cases hiH : i = cHS t
          · subst hiH
            simp [coeffSt, hρ, Function.update_of_ne hTH.symm, Function.update_of_ne hCH.symm, HD.hs]
            exact rdEq_append_false _
          · simp [coeffSt, hρ, Function.update_of_ne hiT, Function.update_of_ne hiC, Function.update_of_ne hiH]
            exact RdEq.refl _
  obtain ⟨τ6, E6, S6⟩ := walks_exec f cap ρ hw' kh (16 * kh + 8) hready req hin B Win hB hWin (by omega) hcapK Tw τ5
    hσ
  have hOUT6 := WXExec.avoids E6 (walksP_avoids f.program)
  -- the table head back to the start of the table word
  set I6 := coeffSt (ρ.setv cNX 0) kh (walkDigits kh 8 (2 ^ (kh * 8)))
    (Tw ++ tableMarks (fun i => Rv (req i)) (2 ^ (kh * 8))) with hI6
  set J := marks (natWord Q) ++ countField π.length (Algorithm.CellCall.prefixValue π) with hJ
  set U := tableWord kh (fun i => Rv (req i)) with hU
  have h6T : I6.st (cT t) = J ++ [false, false] ++ marks U := by
    have hm : kh * 8 = 8 * kh := Nat.mul_comm _ _
    simp only [hI6, coeffSt, WState.seth_st, WState.sets_st, Function.update_self, hTw, startTable, tableHead, hU,
      tableWord, tableMarks_eq, marks_append, List.append_assoc, hJ, hm]
  have h6Th : I6.sh (cT t) = (I6.st (cT t)).length := by simp [hI6, coeffSt]
  have e7 := sentinelRewind_exec cap (cT t) J U I6 h6T h6Th
  obtain ⟨τ7, E7, S7⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim (WXExec.wm e7) τ6 S6
  have hOUT7 := WXExec.avoids E7 (show WMX.Avoids (cOUT t) (.wm (sentinelRewind (cT t))) by
    simp [WMX.Avoids, WM.Avoids, sentinelRewind, hTO])
  -- the framed table after the child input
  have hsh7 : τ7.sh (cT t) = (J ++ [false, false]).length := by rw [S7.sh]; simp
  have hT7 : ∀ q, readTapeBit (τ7.st (cT t)) (τ7.sh (cT t) + q) = readTapeBit (marks U ++ []) q := by
    intro q
    rw [hsh7, ← S7.st (cT t), List.append_nil]
    simp only [WState.seth_st, h6T]
    exact rtb_pre _ _ q
  have hval7 : ∀ r, r ≠ cNX → τ7.val r = τ5.val r := by
    intro r hr
    rw [S7.val]
    simp [hI6, coeffSt, hρ, Function.update_of_ne hr]
  obtain ⟨τ8, E8, hout⟩ := tableTail_exec cap τ7 (cT t) (cOUT t) hTO w U hT7
    (hOUT7.1.trans (hOUT6.1.trans HD.out)) (hOUT7.2.trans (hOUT6.2.trans HD.outh))
    (by rw [hval7 _ (by pdst)]; exact HD.ro) (by rw [hval7 _ (by pdst)]; exact HD.ri) hcapU
  refine ⟨τ8, WXExec.mono (WXExec.seq E5 (WXExec.seq E6 (WXExec.seq E7 E8))) ?_, hout⟩
  unfold gammaCost
  simp only [← hkh, ← hhw', ← hU]
  omega

end NearQuarticWires.Control
