import Proof.Quartic.StageCert.PatternSlot

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `def:mask` and `lem:print`, paper/paper.tex: the original finite source request for one actual
edge of the same retained low-first walk. -/
def MomentRequest.edgeRequest {B1 B2 : ℕ} (r : MomentRequest B1 B2) (edge : Fin 8) :
    StageMainMask.StructuralRequest B1 B2 where
  call := r.call
  selected := r.selected
  dispatched := r.dispatched
  witness := r.witness
  left := r.walk (Cells.leftSlot (by decide : 0<4) edge)
  right := r.walk (Cells.rightSlot (by decide : 0<4) edge)

/-- `def:mask` and `lem:print`, paper/paper.tex: the shared source returns the literal structural
factor in the original integer walk polynomial. -/
theorem MomentRequest.edgeRequest_bit {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (edge : Fin 8) :
    StageMainMask.structuralBit (r.edgeRequest edge)=
      StagePrint.callStructural r.call r.rules r.walk edge := by
  have he := Cells.slots_cellOf (by decide : 0<4) r.walk edge
  change (Builder.columnData r.call r.rules r.witness ⟨0,Nat.two_pow_pos _⟩).structural
      (r.walk (Cells.leftSlot (by decide : 0<4) edge),
        r.walk (Cells.rightSlot (by decide : 0<4) edge))=_
  rw [he]
  rfl

/-- `sec:walks` and `lem:print`, paper/paper.tex: decode the actual row and column indices of one edge
by bounded binary radix arithmetic. -/
def readEdgePatterns (edge : Fin 8) : St VV MM :=
  .seq (readPatternSlot (Cells.leftSlot (by decide : 0<4) edge).val sourceEdgeLeft)
    (readPatternSlot (Cells.rightSlot (by decide : 0<4) edge).val sourceEdgeRight)

/-- `sec:walks`, `lem:print` and `prop:time`, paper/paper.tex: the exact computed edge
indices use at most fourteen divisions, with all input bytes and retained
source records preserved. -/
theorem readEdgePatterns_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (edge : Fin 8) (a : DS VV MM) (hc : Cst a)
    (hb : a.env patternBase=r.selected.1.N)
    (hi : a.env sourceTermIndex=r.index.val) (hfit : 2*r.selected.1.N≤2^C.Wd) :
    Hs C (readEdgePatterns edge) a 71 (fun z=>
      z.env sourceEdgeLeft=(r.edgeRequest edge).left.val ∧
      z.env sourceEdgeRight=(r.edgeRequest edge).right.val ∧
      z.sh=a.sh ∧ Cst z ∧
      Fr a z [sourceEdgeLeft,sourceEdgeRight,patternRemaining,patternQuotient,patternRemainder]) := by
  have hN : 0<r.selected.1.N := lt_of_lt_of_le (by decide : 0<2)
    (Cells.ParameterRules.N_ge_two r.rules)
  unfold readEdgePatterns
  apply Hx.hs
  refine Hs.then (readPatternSlot_run C r.selected.1.N r.index.val
    (Cells.leftSlot (by decide : 0<4) edge).val sourceEdgeLeft (by decide) (by decide)
    a hc hN hb hi hfit)
    (fun b ⟨bl,bs,bc,bf⟩ n1 hn1=>?_)
  refine Hs.last (readPatternSlot_run C r.selected.1.N r.index.val
    (Cells.rightSlot (by decide : 0<4) edge).val sourceEdgeRight (by decide) (by decide)
    b bc hN ((bf _ (by decide)).trans hb) ((bf _ (by decide)).trans hi) hfit)
    (fun z ⟨zr,zs,zc,zf⟩ n2 hn2=>?_)
  refine ⟨⟨(zf _ (by decide)).trans bl,zr,zs.trans bs,zc,
    (bf.weaken (by decide)).trans (zf.weaken (by decide))⟩,?_⟩
  have hl := (Cells.leftSlot (by decide : 0<4) edge).isLt
  have hr := (Cells.rightSlot (by decide : 0<4) edge).isLt
  omega

end NearQuarticWires.StageCert.Tokens
