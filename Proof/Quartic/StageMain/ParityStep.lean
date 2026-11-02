import Proof.Quartic.StageMain.ParityBit
import Proof.Gates.Dispatch.Walk

/-!
# Consuming one literal parity index

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Each self-delimiting index is parsed,
its bounded coordinate is read from the retained input point, and the
running parity is updated. Duplicate indices are consumed separately.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

def parityStep : St VV := .seq readNat (.seq parityChoose parityXor)
def parityStepScratch : List (Fin VV) := readNatT ++ parityChooseScratch ++ [parityResult]

theorem parityStep_spec {C : Ctx} (a : DS VV) (hc : Cst a) (i : ℕ) (old : Bool)
    (rest : List Bool) (hin : C.cw.drop a.cp = natWord i ++ rest)
    (hold : a.env parityResult = old.toNat)
    (hW : natBitLength i + 2 ≤ C.Wd) (hN : a.env callArity + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C parityStep a (30 * natBitLength i + 5 * a.env callArity + 116) (fun b =>
      b.env parityResult = (xor old (coordinateBit (a.env callArity) (a.env pointSaved) i)).toNat ∧
      b.cp = a.cp + (natWord i).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b parityStepScratch) := by
  refine Hx.hs (Hs.then (readNat_spec a hc i rest hin hW hL)
    (fun b ⟨bi, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bn : b.env callArity = a.env callArity := bf _ (by decide)
  have bx : b.env pointSaved = a.env pointSaved := bf _ (by decide)
  refine Hs.then (parityChoose_spec b bc i bi (by rw [bn]; exact hN) (by rw [bx]; exact hpoint))
    (fun d ⟨db, dp, dw, dout, dc, df⟩ n2 hn2 => ?_)
  have dpar : d.env parityResult = old.toNat :=
    (df _ (by decide) (by decide)).trans ((bf _ (by decide)).trans hold)
  refine Hs.last (parityXor_spec d dc old _ dpar db) ?_
  rintro e ⟨ep, ecp, ew, eo, ec, ef⟩ n3 hn3
  refine ⟨⟨by rw [ep, bn, bx], by rw [ecp, dp, bp], ew.trans (dw.trans bw),
    eo.trans (dout.trans bo), ec,
    FrS.trans (bf.toS.weaken (by decide)) (FrS.trans (df.weaken (by decide)) (ef.toS.weaken (by decide)))⟩, ?_⟩
  rw [bn] at hn2
  omega

end NearQuarticWires.StageMain
