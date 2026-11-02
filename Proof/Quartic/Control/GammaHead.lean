import Proof.Quartic.Control.Table

/-!
# The coefficient stage: the phase before the walks

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `cor:conditional`. Before the
walks, the coefficient stage copies the child input to the output, reads the seed parameters and the prefix into
the fixed part of the requests, and prepares the table and the walk index (`gammaHead_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicGates.Close.Interfaces (Call)

/-- The phase before the walks. -/
noncomputable def headP (t : ℕ) : WMX (cns t) lnr :=
  .seq (.seq (copyLoop false (cIN t) (cOUT t) rO rI) (.wm (NearCubicGates.Close.Codec.rewindLoop (cIN t) rI)))
    (.wm (.seq (seedHead (cIN t) (cHS t) (cT t)) (.seq (tailSkip (cIN t))
      (.seq (prefixHead (cIN t) (cHS t) (cT t)) (walkStart (cHS t) (cCT t) (cT t))))))

/-- The state before the first walk. -/
structure HeadDone (t : ℕ) (τ : WState (cns t) lnr) (w hw Tw : List Bool) (kh : ℕ) : Prop where
  hs : τ.st (cHS t) = marks hw
  hsh : τ.sh (cHS t) = 0
  ct : τ.st (cCT t) = (walkDigits kh 8 0).flatMap (countField kh)
  cth : τ.sh (cCT t) = 0
  tt : τ.st (cT t) = Tw
  tth : τ.sh (cT t) = Tw.length
  ruler : τ.st (cL t) = []
  rulerh : τ.sh (cL t) = 0
  b : ∀ j, τ.st (cbank t j) = []
  bh : ∀ j, τ.sh (cbank t j) = 0
  ta : τ.st (cTA t) = []
  tah : τ.sh (cTA t) = 0
  ga : τ.st (cGA t) = []
  gah : τ.sh (cGA t) = 0
  out : τ.st (cOUT t) = marks w
  outh : τ.sh (cOUT t) = 2 * w.length
  rs : ∀ i, τ.val (rS i) = 0
  op : τ.val cOP = 0
  c : τ.val cC = 0
  d : τ.val cD = 0
  lc : τ.val cLC = 16 * kh + 8
  y : ∀ i, τ.val (cY i) = 0
  r : ∀ i, τ.val (cR i) = 0
  z0 : τ.val (cZ 0) = 0
  z1 : τ.val (cZ 1) = 0
  z2 : τ.val (cZ 2) = 0
  z3 : τ.val (cZ 3) = kh
  z4 : τ.val (cZ 4) = 0
  nx : τ.val cNX = 1
  ro : τ.val rO = 2 * w.length
  ri : τ.val rI = 0

/-- The fixed part of the requests. -/
def headWord (ell kh Q : ℕ) (π : List Bool) : List Bool :=
  seedWord ell kh Q ++ (natWord π.length ++ natWord (Algorithm.CellCall.prefixValue π))

/-- The table before the walks. -/
def startTable (Q kh : ℕ) (π : List Bool) : List Bool :=
  marks (natWord Q) ++ countField π.length (Algorithm.CellCall.prefixValue π) ++ tableHead kh

/-- The cost of the phase before the walks. -/
def headCost (c : Call) (xs ys zs ps ws fs : List ℕ) (k Q ell : ℕ) (wp cb π w : List Bool) : ℕ :=
  w.length * 52 + 1 + 1 + (5 * (2 * w.length) + 1) + 1 + (seedHeadCost c xs ys k Q ell + 1 +
    (tailCost zs ps ws fs wp cb + 1 + (prefixCost π.length + 1 +
      walkStartCost (k / 2) (2 * (headWord ell (k / 2) Q π).length))))

theorem gammaHead_exec (cap t : ℕ) (w : List Bool) (c : Call) (xs ys zs ps ws fs : List ℕ) (k Q ell : ℕ)
    (wp cb π : List Bool)
    (hw : w = seedPre c xs k ys Q ell ++ (tailWord zs ps ws fs wp cb ++ frame π))
    (hxs : xs.length = 6) (hys : ys.length = 10) (hzs : zs.length = 18) (hws : ws.length = 9)
    (hfit : ReadFits cap c xs k) (hyfit : ∀ y ∈ ys, natBitLength y + 1 ≤ cap)
    (hzf : ∀ x ∈ zs, natBitLength x + 1 ≤ cap) (hwf : ∀ x ∈ ws, natBitLength x + 1 ≤ cap)
    (hpf : ListFits cap ps) (hff : ListFits cap fs)
    (hcapW : 6 * w.length + 6 ≤ cap)
    (hcapS : 4 * (seedWord ell (k / 2) Q).length + k + 6 * natBitLength k + 20 ≤ cap)
    (hcapP : 2 * (seedWord ell (k / 2) Q).length + 12 * π.length + 30 ≤ cap)
    (hcapT : 2 * (headWord ell (k / 2) Q π).length + 40 * (k / 2) + 20 + 16 * (k / 2) + 8 ≤ cap) :
    ∃ τ, WXExec cap (headP t) (gammaStart t w) τ (headCost c xs ys zs ps ws fs k Q ell wp cb π w) ∧
      HeadDone t τ w (headWord ell (k / 2) Q π) (startTable Q (k / 2) π) (k / 2) := by
  have hIO : cIN t ≠ cOUT t := cne _ (by simp [cIN, cOUT])
  have hIH : cIN t ≠ cHS t := cne _ (by simp [cIN, cHS])
  have hIT : cIN t ≠ cT t := cne _ (by simp [cIN, cT])
  have hHT : cHS t ≠ cT t := cne _ (by simp [cHS, cT])
  have hHC : cHS t ≠ cCT t := cne _ (by simp [cHS, cCT])
  have hCT : cCT t ≠ cT t := cne _ (by simp [cCT, cT])
  have E1 := inputCopy_exec cap t w hcapW
  set σ1 := appendO (gammaStart t w) (cOUT t) rO (marks w) with hσ1
  have h1IN : σ1.st (cIN t) = marks (seedPre c xs k ys Q ell ++ (tailWord zs ps ws fs wp cb ++ frame π)) ++ [false] := by
    rw [hσ1, appendO_st, Function.update_of_ne hIO, gammaStart_st, ← hw]
    simp [cIN, NearCubicGates.Close.Codec.frame_eq_marks]
  have E2 := seedHead_exec cap (cIN t) (cHS t) (cT t) hIH hIT hHT σ1 c xs ys k Q ell _ [false] h1IN
    (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (fun i => by fin_cases i <;> simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT])
    hfit hxs hys hyfit hcapS
  set σ2 := (((appendO (appendO σ1 (cT t) (cY 0) (marks (natWord Q))) (cHS t) rH (marks (seedWord ell (k / 2) Q))).seth
    (cIN t) (marks (seedPre c xs k ys Q ell)).length).setv (cY 0) 0).setv (cZ 3) (k / 2) with hσ2
  have h2IN : σ2.st (cIN t) = marks (seedPre c xs k ys Q ell) ++ marks (tailWord zs ps ws fs wp cb) ++
      (marks (frame π) ++ [false]) := by
    simp only [hσ2, WState.setv_st, WState.seth_st, appendO_st, Function.update_of_ne hIH, Function.update_of_ne hIT,
      h1IN, marks_append, List.append_assoc]
  have E3 := tailSkip_exec cap (cIN t) zs ps ws fs wp cb hzs hws hzf hwf hpf hff _ _ σ2 h2IN (by simp [hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT])
    (fun i => by fin_cases i <;> simp [hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT])
  set σ3 := σ2.seth (cIN t) ((marks (seedPre c xs k ys Q ell)).length + (marks (tailWord zs ps ws fs wp cb)).length)
    with hσ3
  have h3IN : σ3.st (cIN t) = (marks (seedPre c xs k ys Q ell) ++ marks (tailWord zs ps ws fs wp cb)) ++
      marks (frame π) ++ [false] := by
    simp only [hσ3, WState.seth_st, h2IN, List.append_assoc]
  have h3H : σ3.val rH = 2 * (seedWord ell (k / 2) Q).length := by simp [hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [marks_length]
  have E4 := prefixHead_exec cap (cIN t) (cHS t) (cT t) hIH hIT hHT σ3 π _ [false] h3IN (by simp [hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp)
    (by simp [hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (fun i => by fin_cases i <;> simp [hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (fun i => by fin_cases i <;> simp [hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by rw [h3H]; omega)
  set σ4 := ((appendO (appendO σ3 (cT t) (cY 1) (countField π.length (Algorithm.CellCall.prefixValue π))) (cHS t) rH
    (marks (natWord π.length ++ natWord (Algorithm.CellCall.prefixValue π)))).seth (cIN t)
      ((marks (seedPre c xs k ys Q ell) ++ marks (tailWord zs ps ws fs wp cb)).length + (marks (frame π)).length)).setv
        (cY 1) 0 with hσ4
  have h4H : σ4.val rH = 2 * (headWord ell (k / 2) Q π).length := by
    simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [headWord, marks_length] <;> ring
  have E5 := walkStart_exec cap (cHS t) (cCT t) (cT t) hHC hHT hCT σ4 (k / 2) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT])
    (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]) (by rw [h4H]; simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [headWord, marks_length] <;> ring)
    (by rw [h4H]; simp [hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> omega)
  rw [h4H] at E5
  refine ⟨_, WXExec.seq E1 (WXExec.wm (WExec.seq E2 (WExec.seq E3 (WExec.seq E4 E5)))), ?_⟩
  set σ5 := ((((((appendO (appendO σ4 (cT t) rT (tableHead (k / 2))) (cCT t) (cY 3)
    ((walkDigits (k / 2) 8 0).flatMap (countField (k / 2)))).setv (cY 3) 0).seth (cCT t) 0).setv cLC
      (16 * (k / 2) + 8)).setv rH 0).seth (cHS t) 0).setv cNX 1 with hσ5
  exact {
    hs := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [headWord, seedWord, marks_append]
    hsh := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    ct := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    cth := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    tt := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [startTable]
    tth := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [startTable, marks_length] <;> ring
    ruler := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    rulerh := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    b := fun j => by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> split_ifs <;> first | omega | rfl | simp
    bh := fun j => by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> split_ifs <;> first | omega | rfl | simp
    ta := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    tah := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    ga := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    gah := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    out := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    outh := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [marks_length]
    rs := fun i => by fin_cases i <;> simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    op := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    c := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    d := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    lc := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    y := fun i => by fin_cases i <;> simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    r := fun i => by fin_cases i <;> simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    z0 := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    z1 := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    z2 := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    z3 := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    z4 := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    nx := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT]
    ro := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] <;> simp [marks_length]
    ri := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, NearCubicGates.Close.Expand.PolyTab.idealStart, Function.update_apply, cIN, cOUT, cHS, cCT, cT, cL, cTA, cGA, cbank, cY, cR, cZ, cD, cLC, cNX, cOP, cC, rS, rO, rI, rH, rT] }

end NearQuarticWires.Control
