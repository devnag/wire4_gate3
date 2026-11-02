import Proof.Quartic.StageMain.ParityStep
import Proof.Gates.Dispatch.ParseCirc

/-!
# The literal parity-index loop

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Every encoded index is consumed in list
order. Its in-range input bit is folded by exclusive-or, so repeated
indices cancel with their actual multiplicity.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

def parityFold (n x : ℕ) (is : List ℕ) : Bool := (is.map (coordinateBit n x)).foldl xor false

def parityLoop : St VV := .loop (.lt parityIndex parityLength) (.seq parityStep (.op (.inc parityIndex)))
def parityLoopScratch : List (Fin VV) := parityIndex :: parityStepScratch

theorem parityLoop_spec {C : Ctx} (is : List ℕ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hi : a.env parityIndex = 0)
    (hn : a.env parityLength = is.length) (hr : a.env parityResult = 0)
    (hin : C.cw.drop a.cp = is.flatMap natWord ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hN : a.env callArity + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (hlen : is.length < 2 ^ C.Wd)
    (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C parityLoop a (is.length * (30 * C.cw.length + 5 * a.env callArity + 120) + 2) (fun b =>
      b.env parityResult = (parityFold (a.env callArity) (a.env pointSaved) is).toNat ∧
      b.cp = a.cp + (is.flatMap natWord).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b parityLoopScratch ∧ b.env parityIndex = is.length ∧ b.env parityLength = is.length) := by
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env parityResult = (parityFold (a.env callArity) (a.env pointSaved) (is.take k)).toNat ∧
    b.env callArity = a.env callArity ∧ b.env pointSaved = a.env pointSaved ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b parityLoopScratch
  have hset : ∀ k b v, P k b → P k (b.set parityIndex v) := by
    rintro k b v ⟨br, bn, bx, bw, bo, bc, bf⟩
    exact ⟨by simpa (config := { decide := true }) using br,
      by simpa (config := { decide := true }) using bn,
      by simpa (config := { decide := true }) using bx, bw, bo,
      bc.set _ _ (by decide), FrS.trans bf (Fr.set _ _ (by decide)).toS⟩
  have hbody : ∀ k (hk : k < is.length) (b : DS VV), P k b →
      b.env parityIndex = k → b.env parityLength = is.length →
      C.cw.drop b.cp = natWord is[k] ++ ((is.drop (k + 1)).flatMap natWord ++ rest) →
      Hs C parityStep b (30 * C.cw.length + 5 * a.env callArity + 116) (fun d =>
        P (k + 1) d ∧ d.env parityIndex = k ∧ d.env parityLength = is.length ∧
        d.cp = b.cp + (natWord is[k]).length) := by
    intro k hk b ⟨br, bn, bx, bw, bo, bc, bf⟩ bi bl hd
    have hl := len_le_of_drop hd
    have hb := natBitLength_le_len is[k]
    refine Hs.mono (parityStep_spec b bc is[k] _ _ hd br (by omega)
      (by rw [bn]; exact hN) hL (by rw [bx]; exact hpoint)) (by rw [bn]; omega) ?_
    rintro d ⟨dr, dp, dw, dout, dc, df⟩
    refine ⟨⟨?_, (df _ (by decide) (by decide)).trans bn,
      (df _ (by decide) (by decide)).trans bx, dw.trans bw, dout.trans bo, dc,
      FrS.trans bf (df.weaken (by decide))⟩,
      (df _ (by decide) (by decide)).trans bi, (df _ (by decide) (by decide)).trans bl, dp⟩
    rw [dr, bn, bx, List.take_succ_eq_append_getElem hk]
    simp only [parityFold, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hh := walk (C := C) is natWord parityIndex parityLength (by decide) parityStep P
    (30 * C.cw.length + 5 * a.env callArity + 116) rest hset hbody hlen a
    ⟨by simpa [parityFold] using hr, rfl, rfl, rfl, rfl, hc, fun _ _ _ => rfl⟩ hi hn hin
  refine Hs.mono hh le_rfl ?_
  rintro b ⟨⟨br, _, _, bw, bo, bc, bf⟩, bi, bn, bcp⟩
  exact ⟨by simpa using br, bcp, bw, bo, bc, bf, bi, bn⟩

end NearQuarticWires.StageMain
