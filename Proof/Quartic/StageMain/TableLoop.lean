import Proof.Quartic.StageMain.TableBit
import Proof.Gates.Dispatch.ParseCirc

/-!
# A sequential lookup in the literal top table

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The loop consumes all entries and returns
exactly the requested Boolean entry, with false for an absent index.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def tableLoop : St VV := .loop (.lt tableIndex tableLength) (.seq tableBit (.op (.inc tableIndex)))
def tableLoopScratch : List (Fin VV) := tableIndex :: tableBitScratch

theorem tableLoop_spec {C : Ctx} (table : List Bool) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hi : a.env tableIndex = 0)
    (hn : a.env tableLength = table.length) (hr : a.env tableResult = 0)
    (hin : C.cw.drop a.cp = table.flatMap bitWord ++ rest)
    (hW : 4 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) (hlen : table.length < 2 ^ C.Wd) :
    Hs C tableLoop a (104 * table.length + 2) (fun b =>
      b.env tableResult = (table.getD (a.env tableTarget) false).toNat ∧
      b.cp = a.cp + (table.flatMap bitWord).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b tableLoopScratch ∧ b.env tableIndex = table.length ∧ b.env tableLength = table.length) := by
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env tableResult = (if a.env tableTarget < k then (table.getD (a.env tableTarget) false).toNat else 0) ∧
    b.env tableTarget = a.env tableTarget ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b tableLoopScratch
  have hp : ∀ k b v, P k b → P k (b.set tableIndex v) := by
    rintro k b v ⟨br, bt, bw, bo, bc, bf⟩
    exact ⟨by simpa (config := { decide := true }) using br,
      by simpa (config := { decide := true }) using bt, bw, bo,
      bc.set _ _ (by decide), Fr.trans bf (Fr.set _ _ (by decide))⟩
  have hb : ∀ k (hk : k < table.length) (b : DS VV), P k b →
      b.env tableIndex = k → b.env tableLength = table.length →
      C.cw.drop b.cp = bitWord table[k] ++ ((table.drop (k + 1)).flatMap bitWord ++ rest) →
      Hs C tableBit b 100 (fun d => P (k + 1) d ∧ d.env tableIndex = k ∧
        d.env tableLength = table.length ∧ d.cp = b.cp + (bitWord table[k]).length) := by
    intro k hk b ⟨br, bt, bw, bo, bc, bf⟩ bi bn hd
    refine Hs.mono (tableBit_spec b bc table[k] _ hd hW hL) le_rfl ?_
    rintro d ⟨dr, dp, dw, dout, dc, df⟩
    refine ⟨⟨?_, (df _ (by decide)).trans bt, dw.trans bw, dout.trans bo, dc,
      Fr.trans bf (df.weaken (by decide))⟩,
      (df _ (by decide)).trans bi, (df _ (by decide)).trans bn, dp⟩
    rw [dr, bi, bt, br]
    by_cases he : k = a.env tableTarget
    · subst he
      simp [hk]
    · by_cases ht : a.env tableTarget < k
      · simp [he, ht, Nat.lt_succ_of_lt ht]
      · have ht' : ¬a.env tableTarget < k + 1 := by omega
        simp [he, ht, ht']
  have hh := walk (C := C) table bitWord tableIndex tableLength (by decide) tableBit P 100 rest hp hb hlen a
    ⟨by simpa using hr, rfl, rfl, rfl, hc, fun _ _ => rfl⟩ hi hn hin
  refine Hs.mono hh (by omega) ?_
  rintro b ⟨⟨br, _, bw, bo, bc, bf⟩, bi, bn, bcp⟩
  refine ⟨?_, bcp, bw, bo, bc, bf, bi, bn⟩
  rw [br]
  split_ifs with ht
  · rfl
  · simp [Nat.le_of_not_gt ht]

end NearQuarticWires.StageMain
