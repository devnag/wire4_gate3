import Proof.Quartic.StageMain.ParityStart
import Proof.Quartic.StageMain.ParityLoop
import Proof.Gates.Interfaces.Counter
import Proof.Quartic.StageMain.ThresholdValue

/-!
# Evaluating the literal parity list

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Reading the header and every index gives
the exact parity of the selected input coordinates. Indices outside the
arity contribute false; repeated indices retain their multiplicity.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def evalParity : St VV := .seq parityStart parityLoop
def evalParityScratch : List (Fin VV) := parityStartScratch ++ parityLoopScratch

theorem evalParity_spec {C : Ctx} (is : List ℕ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hin : C.cw.drop a.cp = listWord natWord is ++ rest)
    (hW : C.cw.length + 3 ≤ C.Wd) (hN : a.env callArity + 2 ≤ C.Wd)
    (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C evalParity a (200 * (C.cw.length + a.env callArity + 2) ^ 2) (fun b =>
      b.env parityResult = (parityFold (a.env callArity) (a.env pointSaved) is).toNat ∧
      b.cp = a.cp + (listWord natWord is).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b evalParityScratch) := by
  have hi := hin
  simp only [listWord, List.append_assoc] at hi
  have hl := len_le_of_drop hin
  have hcount := length_le_flatMap is natWord (fun i => by rw [natWord_length]; omega)
  have hnb := natBitLength_le_len is.length
  have hflat : (is.flatMap natWord).length ≤ C.cw.length := by
    simp only [listWord, List.length_append] at hl
    omega
  have hnat : natBitLength is.length ≤ C.cw.length := by
    simp only [listWord, List.length_append] at hl
    omega
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (parityStart_spec a hc is.length _ hi (by omega) hL)
    (fun b ⟨bn, bi, br, bcp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bx : b.env pointSaved = a.env pointSaved := bf _ (by decide) (by decide)
  have bar : b.env callArity = a.env callArity := bf _ (by decide) (by decide)
  have binput : C.cw.drop b.cp = is.flatMap natWord ++ rest := by rw [bcp, drop_adv hi]
  refine Hs.last (parityLoop_spec is rest b bc bi bn br binput (by omega)
    (by rw [bar]; exact hN) hL (by omega) (by rw [bx]; exact hpoint)) ?_
  rintro e ⟨er, ep, ew, eo, ec, ef, _, _⟩ n2 hn2
  refine ⟨⟨by rw [er, bar, bx], ?_, ew.trans bw, eo.trans bo, ec,
    FrS.trans (bf.weaken (by decide)) (ef.weaken (by decide))⟩, ?_⟩
  · rw [ep, bcp]
    simp only [listWord, List.length_append, Nat.add_assoc]
  · rw [bar] at hn2
    have hh := Nat.mul_le_mul_right (30 * C.cw.length + 5 * a.env callArity + 120) (hcount.trans hflat)
    nlinarith only [hn1, hn2, hnat, hh]

/-- The packed-point fold is the parity predicate in the literal call. -/
theorem parityFold_eq (c : Call) (x : ℕ) :
    parityFold c.n x c.parity = c.parityOf (packedPoint c.n x) := by
  unfold parityFold Call.parityOf
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < c.n <;> simp [coordinateBit, packedPoint, hi]

end NearQuarticWires.StageMain
