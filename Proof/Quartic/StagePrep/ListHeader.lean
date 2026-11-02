import Proof.Gates.Dispatch.Arith2
import Proof.Gates.Dispatch.Walk

/-!
# Reading an encoded list header

Paper: the normalized call encoding in paper/paper.tex and the preparation cost of `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairRepresentation

/-- The list-header reader of `sec:counting`, paper/paper.tex stores
the exact length and initializes the index. -/
def readListHeader (iv nv : Fin VV) : St VV :=
  .seq readNat (.seq (.op (.copy nv t3)) (.op (.zero iv)))

/-- Reading the list header of `sec:counting`, paper/paper.tex
preserves all fields except the two designated counters and the
integer-reader scratch registers. -/
theorem readListHeader_spec (C : Ctx) (iv nv : Fin VV)
    (hin : iv ≠ nv) (hnt : nv ≠ t3)
    (hisafe : iv ∉ [vZ, v1, v2, vPOS])
    (hnsafe : nv ∉ [vZ, v1, v2, vPOS])
    (a : DS VV) (hc : Cst a) (l : ℕ) (rest : List Bool)
    (hcw : C.cw.drop a.cp = natWord l ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C (readListHeader iv nv) a (30 * natBitLength l + 35) (fun b =>
      b.env iv = 0 ∧ b.env nv = l ∧
      b.cp = a.cp + (natWord l).length ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b (iv :: nv :: readNatT)) := by
  have hnb : natBitLength l ≤ C.cw.length := by
    have hlen := congrArg List.length hcw
    have hbit := natBitLength_le_len l
    simp only [List.length_drop, List.length_append] at hlen
    omega
  unfold readListHeader
  refine Hs.mono (Hs.seq (t2 := 3) (readNat_spec a hc l rest hcw (by omega) hL) ?_)
    (by omega) (fun _ h => h)
  rintro b ⟨hb3, _, hbcp, hbwq, hbout, hbc, hbfr⟩
  refine Hs.seq (t2 := 1) (hs_copy C nv t3 b hnt) ?_
  rintro d rfl
  refine Hs.mono (hs_zero C iv _) le_rfl ?_
  rintro e rfl
  refine ⟨by simp, ?_, hbcp, hbwq, hbout,
    (hbc.set nv _ hnsafe).set iv _ hisafe, ?_⟩
  · rw [DS.set_env_ne _ _ hin.symm, DS.set_env_self, hb3]
  · apply Fr.trans (Fr.weaken hbfr (by intro y hy; simp [hy]))
    exact Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp))

end NearQuarticWires.StagePrep
