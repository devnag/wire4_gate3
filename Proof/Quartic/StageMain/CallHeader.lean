import Proof.Quartic.StageMain.ParityBit
import Proof.Gates.Dispatch.Walk

/-!
# Reading the arity and kind of a counting call

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The two leading natural-number words
select the arity and the single, pair, or parity predicate. The retained
sample and all surrounding live registers are preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

def callKind : Fin VV := ⟨67, by decide⟩
def firstValue : Fin VV := ⟨68, by decide⟩
def secondValue : Fin VV := ⟨69, by decide⟩

def callHeader : St VV := .seq readNat (.seq (.op (.copy callArity t3))
  (.seq readNat (.op (.copy callKind t3))))
def callHeaderScratch : List (Fin VV) := readNatT ++ [callArity, callKind]

theorem callHeader_spec {C : Ctx} (a : DS VV) (hc : Cst a) (n tag : ℕ) (rest : List Bool)
    (hin : C.cw.drop a.cp = natWord n ++ (natWord tag ++ rest))
    (hN : natBitLength n + 2 ≤ C.Wd) (hT : natBitLength tag + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C callHeader a (30 * natBitLength n + 30 * natBitLength tag + 66) (fun b =>
      b.env callArity = n ∧ b.env callKind = tag ∧
      b.cp = a.cp + (natWord n).length + (natWord tag).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b callHeaderScratch) := by
  refine Hx.hs (Hs.then (readNat_spec a hc n _ hin hN hL)
    (fun b ⟨bn, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C callArity t3 b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  have bi : C.cw.drop (b.set callArity (b.env t3)).cp = natWord tag ++ rest := by
    rw [DS.set_cp, bp, drop_adv hin]
  refine Hs.then (readNat_spec _ (bc.set _ _ (by decide)) tag rest bi hT hL)
    (fun e ⟨et, _, ep, ew, eo, ec, ef⟩ n3 hn3 => ?_)
  refine Hs.last (hs_copy C callKind t3 e (by decide)) ?_
  rintro f rfl n4 hn4
  refine ⟨⟨?_, by simp [et], ?_, ?_, ?_, ec.set _ _ (by decide), ?_⟩, by omega⟩
  · rw [DS.set_env_ne _ _ (by decide), ef _ (by decide), DS.set_env_self, bn]
  · rw [DS.set_cp, ep, DS.set_cp, bp]
  · simpa using ew.trans bw
  · simpa using eo.trans bo
  · exact Fr.trans (bf.weaken (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (ef.weaken (by decide)) (Fr.set _ _ (by decide))))

end NearQuarticWires.StageMain
