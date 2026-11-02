import Proof.Quartic.StageMain.TableStart
import Proof.Quartic.StageMain.TableLoop

/-!
# Evaluating a literal top table at a signed score

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The header and every table entry are
consumed. The returned bit is the exact list lookup at the signed score
plus its absolute-weight offset, using false for absent entries.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def evalTable : St VV := .seq tableStart tableLoop
def evalTableScratch : List (Fin VV) := tableStartScratch ++ tableLoopScratch

theorem evalTable_spec {C : Ctx} (table : List Bool) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hin : C.cw.drop a.cp = listWord bitWord table ++ rest)
    (hW : C.cw.length + 4 ≤ C.Wd)
    (hadd : a.env scorePositive + a.env topAbsolute < 2 ^ C.Wd) :
    Hs C evalTable a (200 * C.cw.length + 200) (fun b =>
      b.env tableResult = (table.getD ((a.env scorePositive + a.env topAbsolute) - a.env scoreNegative) false).toNat ∧
      b.cp = a.cp + (listWord bitWord table).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b evalTableScratch) := by
  have hi := hin
  simp only [listWord, List.append_assoc] at hi
  have hl := len_le_of_drop hin
  have hcount := length_le_flatMap table bitWord (fun bit => by
    cases bit <;> simp [bitWord])
  have hnb := natBitLength_le_len table.length
  have hflat : (table.flatMap bitWord).length ≤ C.cw.length := by
    simp only [listWord, List.length_append] at hl
    omega
  have hnat : natBitLength table.length ≤ C.cw.length := by
    simp only [listWord, List.length_append] at hl
    omega
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (tableStart_spec a hc table.length _ hi (by omega) hL hadd)
    (fun b ⟨bn, bi, br, bt, bcp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have binput : C.cw.drop b.cp = table.flatMap bitWord ++ rest := by rw [bcp, drop_adv hi]
  refine Hs.last (tableLoop_spec table rest b bc bi bn br binput (by omega) hL (by omega)) ?_
  rintro e ⟨er, ep, ew, eo, ec, ef, _, _⟩ n2 hn2
  refine ⟨⟨by rw [er, bt], ?_, ew.trans bw, eo.trans bo, ec,
    FrS.trans (bf.weaken (by decide)) (ef.toS.weaken (by decide))⟩, by omega⟩
  rw [ep, bcp]
  simp only [listWord, List.length_append, Nat.add_assoc]

end NearQuarticWires.StageMain
