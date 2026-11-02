import Proof.Quartic.StageMain.ScoreList
import Proof.Gates.Dispatch.ParseCirc

/-!
# The physical signed-weight loop

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. A single loop reads every encoded
coefficient exactly once and evaluates its selected positive and negative
contributions. Repeated and zero weights retain their literal positions.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def scoreWeights : St VV :=
  .loop (.lt weightIndex weightLength) (.seq scoreWeight (.op (.inc weightIndex)))

def scoreWeightsScratch : List (Fin VV) := weightIndex :: scoreWeightScratch

theorem scoreWeights_spec {C : Ctx} (ws : List ℤ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hi : a.env weightIndex = 0)
    (hn : a.env weightLength = ws.length)
    (hin : C.cw.drop a.cp = ws.flatMap intWord ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hlen : ws.length < 2 ^ C.Wd) (hpoint : a.env pointWork < 2 ^ C.Wd)
    (hcap : a.env scorePositive + a.env scoreNegative + 3 * (ws.map Int.natAbs).sum + 1 < 2 ^ C.Wd) :
    Hs C scoreWeights a (ws.length * (60 * C.cw.length + 129) + 2) (fun b =>
      b.env scorePositive = a.env scorePositive + positiveScore ws (a.env pointWork) ∧
      b.env scoreNegative = a.env scoreNegative + negativeScore ws (a.env pointWork) ∧
      b.env pointWork = a.env pointWork / 2 ^ ws.length ∧
      b.cp = a.cp + (ws.flatMap intWord).length ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ FrS a b scoreWeightsScratch ∧
      b.env weightIndex = ws.length ∧ b.env weightLength = ws.length) := by
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env scorePositive = a.env scorePositive + positiveScore (ws.take k) (a.env pointWork) ∧
    b.env scoreNegative = a.env scoreNegative + negativeScore (ws.take k) (a.env pointWork) ∧
    b.env pointWork = a.env pointWork / 2 ^ k ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b scoreWeightsScratch
  have hp : ∀ k b v, P k b → P k (b.set weightIndex v) := by
    rintro k b v ⟨bp, bn, bx, bw, bo, bc, bf⟩
    refine ⟨?_, ?_, ?_, bw, bo, bc.set _ _ (by decide),
      FrS.trans bf (Fr.set _ _ (by decide)).toS⟩
    · simpa (config := { decide := true }) using bp
    · simpa (config := { decide := true }) using bn
    · simpa (config := { decide := true }) using bx
  have hb : ∀ k (hk : k < ws.length) (b : DS VV), P k b →
      b.env weightIndex = k → b.env weightLength = ws.length →
      C.cw.drop b.cp = intWord ws[k] ++ ((ws.drop (k + 1)).flatMap intWord ++ rest) →
      Hs C scoreWeight b (60 * C.cw.length + 125) (fun d =>
        P (k + 1) d ∧ d.env weightIndex = k ∧ d.env weightLength = ws.length ∧
        d.cp = b.cp + (intWord ws[k]).length) := by
    intro k hk b ⟨bp, bn, bx, bw, bo, bc, bf⟩ bi bl hd
    have hlength := len_le_of_drop hd
    have hsum : ((ws.take k).map Int.natAbs).sum ≤ (ws.map Int.natAbs).sum := by
      rw [List.map_take]
      exact take_sum_le _ _
    have hbounds := score_bounds (ws.take k) (a.env pointWork)
    have hweight : ws[k].natAbs ≤ (ws.map Int.natAbs).sum := by
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨ws[k], List.getElem_mem hk, rfl⟩)
    have hcapa : b.env scorePositive + b.env scoreNegative + ws[k].natAbs < 2 ^ C.Wd := by
      rw [bp, bn]
      omega
    have hpointb : b.env pointWork < 2 ^ C.Wd := by
      rw [bx]
      exact (Nat.div_le_self _ _).trans_lt hpoint
    refine Hs.mono (scoreWeight_spec b bc ws[k] _ hd hW hL hpointb hcapa) (by omega) ?_
    rintro d ⟨dp, dn, dx, dcp, dw, dout, dc, df⟩
    have hnext := score_take_succ ws k hk (a.env pointWork)
    refine ⟨⟨?_, ?_, ?_, dw.trans bw, dout.trans bo, dc,
      FrS.trans bf (df.weaken (by decide))⟩,
      (df _ (by decide) (by decide)).trans bi, (df _ (by decide) (by decide)).trans bl, dcp⟩
    · rw [dp, bp, bx, hnext.1]
      omega
    · rw [dn, bn, bx, hnext.2]
      omega
    · rw [dx, bx, Nat.div_div_eq_div_mul, pow_succ]
  have hh := walk (C := C) ws intWord weightIndex weightLength (by decide) scoreWeight P
    (60 * C.cw.length + 125) rest hp hb hlen a
    ⟨by simp [positiveScore], by simp [negativeScore], by simp, rfl, rfl, hc,
      fun _ _ _ => rfl⟩ hi hn hin
  refine Hs.mono hh le_rfl ?_
  rintro b ⟨⟨bp, bn, bx, bw, bo, bc, bf⟩, bi, bl, bcp⟩
  exact ⟨by simpa using bp, by simpa using bn, bx, bcp, bw, bo, bc, bf, bi, bl⟩

end NearQuarticWires.StageMain
