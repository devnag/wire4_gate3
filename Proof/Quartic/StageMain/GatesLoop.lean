import Proof.Quartic.StageMain.Gate
import Proof.Quartic.StageMain.GateBits

/-!
# Evaluating the bottom-gate list in occurrence order

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Every literal bottom-gate record is
read and evaluated at the retained point. The resulting Boolean list is
packed in occurrence order, including repeated gates and empty lists.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires
open NearCubicGates.Close.Counter NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def gatesBody : St VV := .seq scoreGate appendGateBit
def gatesLoop : St VV := .loop (.lt gateIndex gateCount) (.seq gatesBody (.op (.inc gateIndex)))
def gatesLoopScratch : List (Fin VV) := gateIndex :: (scoreGateScratch ++ [vJ, gateBits, gatePower])

def gateValues {n : ℕ} (gs : List (NormalizedThresholdGate n)) (x : ℕ) : List Bool :=
  gs.map fun g => g.eval (packedPoint n x)

theorem gatesLoop_spec {C : Ctx} {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hi : a.env gateIndex = 0) (hn : a.env gateCount = gs.length)
    (hb : a.env gateBits = 0) (hp : a.env gatePower = 1)
    (hin : C.cw.drop a.cp = gs.flatMap gateWord ++ rest)
    (hW : C.cw.length + 3 ≤ C.Wd) (hlen : gs.length ≤ C.cw.length)
    (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C gatesLoop a (gs.length * (200 * (C.cw.length + 2) ^ 2 + 45) + 2) (fun b =>
      b.env gateBits = bitsValue (gateValues gs (a.env pointSaved)) ∧
      b.env gatePower = 2 ^ gs.length ∧
      b.cp = a.cp + (gs.flatMap gateWord).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b gatesLoopScratch ∧ b.env gateIndex = gs.length ∧ b.env gateCount = gs.length) := by
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env gateBits = bitsValue (gateValues (gs.take k) (a.env pointSaved)) ∧
    b.env gatePower = 2 ^ k ∧ b.env pointSaved = a.env pointSaved ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b gatesLoopScratch
  have hset : ∀ k b v, P k b → P k (b.set gateIndex v) := by
    rintro k b v ⟨bb, bp, bx, bw, bo, bc, bf⟩
    exact ⟨by simpa (config := { decide := true }) using bb,
      by simpa (config := { decide := true }) using bp,
      by simpa (config := { decide := true }) using bx,
      bw, bo, bc.set _ _ (by decide), FrS.trans bf (Fr.set _ _ (by decide)).toS⟩
  have hbody : ∀ k (hk : k < gs.length) (b : DS VV), P k b →
      b.env gateIndex = k → b.env gateCount = gs.length →
      C.cw.drop b.cp = gateWord gs[k] ++ ((gs.drop (k + 1)).flatMap gateWord ++ rest) →
      Hs C gatesBody b (200 * (C.cw.length + 2) ^ 2 + 41) (fun d =>
        P (k + 1) d ∧ d.env gateIndex = k ∧ d.env gateCount = gs.length ∧
        d.cp = b.cp + (gateWord gs[k]).length) := by
    intro k hk b ⟨bb, bp, bx, bw, bo, bc, bf⟩ bi bn hd
    refine Hx.hs (Hs.then (scoreGate_spec gs[k] b bc _ hd hW (by rw [bx]; exact hpoint))
      (fun d ⟨dg, dp, dw, dout, dc, df⟩ n1 hn1 => ?_))
    have db : d.env gateBits = bitsValue (gateValues (gs.take k) (a.env pointSaved)) :=
      (df _ (by decide) (by decide)).trans bb
    have dpow : d.env gatePower = 2 ^ (gateValues (gs.take k) (a.env pointSaved)).length := by
      rw [df _ (by decide) (by decide), bp]
      simp [gateValues, Nat.min_eq_left hk.le]
    have dgate : d.env gateResult = (gs[k].eval (packedPoint n (a.env pointSaved))).toNat := by rw [dg, bx]
    refine Hs.last (appendGateBit_spec d dc _ _ db dpow dgate (by
      simp only [gateValues, List.length_map, List.length_take]
      omega)) ?_
    rintro e ⟨eb, epow, ep, ew, eo, ec, ef⟩ n2 hn2
    have efull : FrS b e gatesLoopScratch :=
      FrS.trans (df.weaken (by decide)) (ef.weaken (by decide))
    refine ⟨⟨⟨?_, ?_, (efull _ (by decide) (by decide)).trans bx,
      ew.trans (dw.trans bw), eo.trans (dout.trans bo), ec, FrS.trans bf efull⟩,
      ((ef _ (by decide) (by decide)).trans (df _ (by decide) (by decide))).trans bi, (efull _ (by decide) (by decide)).trans bn,
      ep.trans dp⟩, by omega⟩
    · rw [eb, List.take_succ_eq_append_getElem hk]
      simp only [gateValues, List.map_append, List.map_singleton]
    · simpa only [gateValues, List.length_map, List.length_take, Nat.min_eq_left hk.le] using epow
  have hcap : gs.length < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  have hh := walk (C := C) gs gateWord gateIndex gateCount (by decide) gatesBody P
    (200 * (C.cw.length + 2) ^ 2 + 41) rest hset hbody hcap a
    ⟨by simpa [gateValues, bitsValue] using hb, by simpa using hp, rfl, rfl, rfl, hc,
      fun _ _ _ => rfl⟩ hi hn hin
  refine Hs.mono hh le_rfl ?_
  rintro b ⟨⟨bb, bp, _, bw, bo, bc, bf⟩, bi, bn, bcp⟩
  exact ⟨by simpa using bb, bp, bcp, bw, bo, bc, bf, bi, bn⟩

end NearQuarticWires.StageMain
