import Proof.Quartic.StageNativeKidsTail.Machine

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open StageNativeKids StageResize

/-- `prop:time`, paper/paper.tex: the tail's
fixed structural price is quadratic in actual field count and degree
six in signed widths plus the preserved binary count-codec length. -/
theorem tailBudget_polynomial (r : ResizeTailRequest) :
    r.budget≤100000000*(resizeCostConstant+8)^2*(r.stream.fieldCount+1)^2*
      (r.stream.inputWidth+r.stream.outputWidth+(countWord r).length+1)^6 := by
  let V:=r.stream.inputWidth+r.stream.outputWidth+(countWord r).length+1
  let F:=r.stream.fieldCount+1
  let C:=resizeCostConstant
  have hv:1≤V:=by dsimp [V];omega
  have hf:1≤F:=by dsimp [F];omega
  have hs:=r.stream.word_length_le
  have hb:=r.stream.budget_polynomial
  have hwidth:r.stream.inputWidth+r.stream.outputWidth+1≤V:=by dsimp [V];omega
  have hc:(countWord r).length≤V:=by dsimp [V];omega
  have hv3:V≤V^3:=Nat.le_self_pow (by decide) V
  have hvf:V≤F*V^3:=hv3.trans (Nat.le_mul_of_pos_left _ hf)
  have h1:1≤F*V^3:=(Nat.mul_pos hf (Nat.one_le_pow _ _ hv))
  have hB:r.stream.budget≤C*(F*V^3):=by
    have h:=hb.trans (Nat.mul_le_mul_left (C*F) (Nat.pow_le_pow_left hwidth 3))
    simpa only [Nat.mul_assoc] using h
  have hS:r.stream.word.length≤6*(F*V^3):=by
    have h:=hs.trans (Nat.mul_le_mul_left (6*F) hwidth)
    have h':F*V≤F*V^3:=Nat.mul_le_mul_left F hv3
    nlinarith only [h,h']
  have hprice:r.word.length+r.stream.budget+1≤(C+8)*(F*V^3):=by
    change (countWord r++r.stream.word).length+r.stream.budget+1≤_
    rw [List.length_append]
    nlinarith only [hB,hS,hc,hvf,h1]
  calc
    r.budget=100000000*(r.word.length+r.stream.budget+1)^2:=rfl
    _≤100000000*((C+8)*(F*V^3))^2:=Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprice 2)
    _=100000000*(resizeCostConstant+8)^2*(r.stream.fieldCount+1)^2*
        (r.stream.inputWidth+r.stream.outputWidth+(countWord r).length+1)^6:=by
      dsimp [C,F,V]
      ring

end NearQuarticWires.StageNativeKidsTail
