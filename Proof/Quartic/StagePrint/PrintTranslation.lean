import Proof.Quartic.StagePrint.TranslationInit
import Proof.Quartic.StagePrint.TranslationConnection
import Proof.Quartic.StageLift.PrintSource

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:params`, witness (W1) and `lem:print`, paper/paper.tex: the actual decoded PrintRequest source determines its canonical affine translation at a paid polynomial prefix clock. -/
theorem readPrintTranslation_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hdata : StageLift.PrintSourceData r a)
    (hwidth : r.child.call.n+3≤C.Wd) :
    Hs C readTranslation a
      (106+translationCost (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length
        r.child.selected.1.k)
      (fun b=>b.env translation=StagePullback.translationNumber
          (Builder.star r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2))
          (Builder.translation r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2)
            r.child.witness) ∧
        b.ram=a.ram ∧ b.ip=a.ip ∧ b.out=a.out ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b) := by
  let p:=r.child.selected.1
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hk : p.k<r.child.call.n := hs.k_lt_n
  have ef:=readTranslation_run C p
    (Program.witnessPrefix r.child.call p r.child.witness) a hc hdata.scalarFields hdata.witnessBits
    (by simp only [Program.witnessPrefix,List.length_ofFn,Program.witnessReadLength];omega)
    (Nat.pow_lt_pow_right (by decide) (by omega))
    (lt_of_lt_of_le (by norm_num : 7<2^3)
      (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [hdata.scalarCursor,hdata.witnessCursor] at ef
  refine ef.mono le_rfl ?_
  rintro b ⟨bv,br,bi,bo,bs,bc⟩
  refine ⟨?_,br,bi,bo,bs,bc⟩
  exact bv.trans (translationNumber_retained r.child.call hs r.child.witness).symm

end NearQuarticWires.StagePrint.Header
