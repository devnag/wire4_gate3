import Proof.Gates.Dispatch.ParseCirc

/-!
# Consuming the rational-radius field

Paper: `sec:algorithm`, paper/paper.tex, and the call
encoding of `def:class`. Predicate evaluation consumes the
radius's signed numerator and denominator without changing its result.
All three self-delimiting words are read by the binary parser.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def skipRadius : St VV := .seq readNat (.seq readNat readNat)

theorem skipRadius_spec {C : Ctx} (a : DS VV) (hc : Cst a) (q : ℚ) (rest : List Bool)
    (hin : C.cw.drop a.cp = ratWord q ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C skipRadius a (90 * C.cw.length + 94) (fun b =>
      b.cp = a.cp + (ratWord q).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b readNatT) := by
  have hi : C.cw.drop a.cp = natWord (if q.num < 0 then 1 else 0) ++
      (natWord q.num.natAbs ++ (natWord q.den ++ rest)) := by
    simpa only [ratWord, NearCubicGates.Close.Interfaces.intWord, List.append_assoc] using hin
  have hl := len_le_of_drop hin
  have hb0 := natBitLength_le_len (if q.num < 0 then 1 else 0)
  have hb1 := natBitLength_le_len q.num.natAbs
  have hb2 := natBitLength_le_len q.den
  simp only [ratWord, NearCubicGates.Close.Interfaces.intWord, List.length_append] at hl
  refine Hx.hs (Hs.then (readNat_spec a hc _ _ hi (by omega) hL)
    (fun b ⟨_, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bi : C.cw.drop b.cp = natWord q.num.natAbs ++ (natWord q.den ++ rest) := by rw [bp, drop_adv hi]
  refine Hs.then (readNat_spec b bc _ _ bi (by omega) hL)
    (fun d ⟨_, _, dp, dw, dout, dc, df⟩ n2 hn2 => ?_)
  have di : C.cw.drop d.cp = natWord q.den ++ rest := by rw [dp, drop_adv bi]
  refine Hs.last (readNat_spec d dc _ rest di (by omega) hL) ?_
  rintro e ⟨_, _, ep, ew, eo, ec, ef⟩ n3 hn3
  refine ⟨⟨?_, ew.trans (dw.trans bw), eo.trans (dout.trans bo), ec,
    Fr.trans bf (Fr.trans df ef)⟩, by omega⟩
  rw [ep, dp, bp]
  simp only [ratWord, NearCubicGates.Close.Interfaces.intWord, List.length_append, Nat.add_assoc]

end NearQuarticWires.StageMain
