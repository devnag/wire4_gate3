import Proof.Quartic.StageTupleOuter.SharpParts

/-!
# The sharp request-level tuple ledger

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`budget_sharp`: for every request and every child bound `mc ≥ 1` of its original child pools, the cold
tuple printer's clock is at most `C · censusMagnitude(r, mc)^E · ((1+17G·mc)^(2D) + |termsWord| + 1)`.
The Terms bytes enter only linearly (preparation, loading), the Terms count only through its square inside
the census (initialization), the loop through the SUM of its monomial clocks against the weighted census,
and the final copy through the record stream, which is a fixed record size times the same census.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StageTuple

/-- The final arithmetic of the ledger. -/
theorem sharp_arith (c X T Bs PLC KIC CSC O Cs Es Cm Em : ℕ) (hc : 1 ≤ c)
    (hBs : Bs ≤ Cs*(4*c+2*T+31)+Cs*c^Es)
    (hPLC : PLC ≤ 12*T+400*c+700)
    (hKIC : KIC ≤ 20000*c^2+2000*X+3000)
    (hCSC : CSC ≤ Cm*c^Em*X+4*X+1)
    (hO : O ≤ 15*c^2*X) :
    4*Bs+4*(2*(PLC+KIC+CSC+200*(O+1)+1000)+2)+12 ≤
      (1000*(Cs+Cm+10^6))*c^(Es+Em+2)*(X+T+1) := by
  obtain ⟨P,hP⟩ : ∃P,P=c^(Es+Em+2) := ⟨_,rfl⟩
  have h1 : c^Es ≤ P := by rw [hP];exact Nat.pow_le_pow_right hc (by omega)
  have h2 : c^Em ≤ P := by rw [hP];exact Nat.pow_le_pow_right hc (by omega)
  have h3 : c^2 ≤ P := by rw [hP];exact Nat.pow_le_pow_right hc (by omega)
  have h4 : c ≤ P := by
    rw [hP]
    calc
      c=c^1 := (pow_one c).symm
      _ ≤ _ := Nat.pow_le_pow_right hc (by omega)
  have h5 : 1 ≤ P := le_trans hc h4
  have a1 : Cs*c^Es ≤ Cs*P := Nat.mul_le_mul_left _ h1
  have a2 : Cs*c ≤ Cs*P := Nat.mul_le_mul_left _ h4
  have a3 : Cm*c^Em*X ≤ Cm*P*X := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
  have a4 : c^2*X ≤ P*X := Nat.mul_le_mul_right _ h3
  have a5 : X ≤ P*X := Nat.le_mul_of_pos_left _ h5
  have a6 : T ≤ P*T := Nat.le_mul_of_pos_left _ h5
  have a7 : Cs*T ≤ Cs*(P*T) := Nat.mul_le_mul_left _ a6
  have a8 : Cs ≤ Cs*P := Nat.le_mul_of_pos_right _ h5
  have hfin : (1000*(Cs+Cm+10^6))*P*(X+T+1)=1000*(Cs*(P*X))+1000*(Cs*(P*T))+1000*(Cs*P)+1000*(Cm*P*X)+
      1000*(Cm*(P*T))+1000*(Cm*P)+10^9*(P*X)+10^9*(P*T)+10^9*P := by ring
  rw [←hP,hfin]
  have b1 : 0 ≤ Cs*(P*X) := Nat.zero_le _
  have b2 : 0 ≤ Cm*(P*T) := Nat.zero_le _
  have b3 : 0 ≤ Cm*P := Nat.zero_le _
  have e1 : Cs*(4*c+2*T+31)=4*(Cs*c)+2*(Cs*T)+31*Cs := by ring
  rw [e1] at hBs
  have e2 : 15*c^2*X=15*(c^2*X) := by ring
  rw [e2] at hO
  generalize Cs*(P*X)=Y1 at *
  generalize Cs*(P*T)=Y2 at *
  generalize Cs*P=Y3 at *
  generalize Cm*P*X=Y4 at *
  generalize Cm*(P*T)=Y5 at *
  generalize Cm*P=Y6 at *
  generalize P*X=Y7 at *
  generalize P*T=Y8 at *
  generalize Cs*c^Es=Z1 at *
  generalize Cs*c=Z2 at *
  generalize Cm*c^Em*X=Z3 at *
  generalize c^2*X=Z4 at *
  generalize Cs*T=Z5 at *
  generalize c^2=Z6 at *
  linarith

variable {B : StageNativeKids.NativeKidsRequest → ℕ}
  {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
    StageNativeKids.NativeKidsRequest.output B}
  {nativePrice : NativeStagePrice B}

/-- `lem:print` and `prop:time`, paper/paper.tex: the sharp request-level
clock of the cold tuple printer. -/
theorem budget_sharp (M : TermStageMachine native nativePrice) {Bs : TermCutRequest → ℕ}
    (hBs : TupleSetupCost Bs) :
    ∃ C E : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ ∀ (r : TermCutRequest) (mc : ℕ), 1 ≤ mc →
      (∀ i, (r.toRowContext.nativeKids i).length ≤ mc) →
        termCutBudget M Bs r ≤ C * (r.censusMagnitude mc) ^ E *
          ((1 + 17 * (Builder.allGates r.header.call).length * mc) ^ (2 * r.degree) +
            (termsWord r.terms).length + 1) := by
  obtain ⟨Cs,Es,hS⟩:=hBs
  obtain ⟨Cm,Em,_,_,hM⟩:=M.price
  refine ⟨1000*(Cs+Cm+10^6),Es+Em+2,by norm_num;omega,by omega,fun r mc hmc hkids=>?_⟩
  have hc1 : 1 ≤ r.censusMagnitude mc := by unfold TermCutRequest.censusMagnitude;omega
  have hSSM : r.setupStructuralMagnitude+r.rowDimension ≤ r.censusMagnitude mc := by
    unfold TermCutRequest.censusMagnitude;omega
  have hW : r.stackWidth+2 ≤ r.censusMagnitude mc := by
    unfold TermCutRequest.censusMagnitude TermCutRequest.setupStructuralMagnitude;omega
  have hBs' : Bs r ≤ Cs*(4*r.censusMagnitude mc+2*(termsWord r.terms).length+31)+
      Cs*(r.censusMagnitude mc)^Es := by
    have h1:=hS r
    have h2:=word_length_le r
    have h3 : r.setupStructuralMagnitude^Es ≤ (r.censusMagnitude mc)^Es := Nat.pow_le_pow_left (by omega) _
    calc
      Bs r ≤ Cs*(r.word.length+1)+Cs*r.setupStructuralMagnitude^Es := h1
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (Nat.mul_le_mul_left _ h3)
  have hPLC : r.preparedLoadCost ≤ 12*(termsWord r.terms).length+400*r.censusMagnitude mc+700 := by
    rw [preparedLoadCost_eq]
    have:=preparedWord_length_le r
    omega
  have hKIC : kernelInitializeCost r ≤ 20000*(r.censusMagnitude mc)^2+
      2000*(1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)+3000 := by
    have h:=kernelInitializeCost_le r mc hmc
    have q1 : (r.stackWidth+2)^2 ≤ (r.censusMagnitude mc)^2 := Nat.pow_le_pow_left hW 2
    have q2 : (r.rowDimension+2)^2 ≤ (3*r.censusMagnitude mc)^2 := Nat.pow_le_pow_left (by omega) 2
    rw [mul_pow] at q2
    generalize (r.censusMagnitude mc)^2=Q at q1 q2 ⊢
    generalize (1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)=X at h ⊢
    generalize (r.stackWidth+2)^2=A at h q1
    generalize (r.rowDimension+2)^2=D at h q2
    omega
  have hCSC:=countedSourceCost_le (M.cost r) r mc (Cm*(r.censusMagnitude mc)^Em)
    (fun k hk=>hM r mc hmc hkids k hk) hmc
  have hO : r.output.length ≤ 15*(r.censusMagnitude mc)^2*
      (1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree) := by
    have h:=output_length_le r mc hmc hkids
    have q : (r.rowDimension+2)*(2*(r.stackWidth+1)+1) ≤ 15*(r.censusMagnitude mc)^2 := by
      have:=Nat.mul_le_mul (show r.rowDimension+2 ≤ 3*r.censusMagnitude mc by omega)
        (show 2*(r.stackWidth+1)+1 ≤ 2*r.censusMagnitude mc by omega)
      nlinarith
    exact h.trans (Nat.mul_le_mul_right _ q)
  unfold termCutBudget tupleCoreCost
  exact sharp_arith _ _ _ _ _ _ _ _ Cs Es Cm Em hc1 hBs' hPLC hKIC hCSC hO

end NearQuarticWires.StageTupleOuter
