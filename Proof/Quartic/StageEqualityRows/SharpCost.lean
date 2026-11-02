import Proof.Quartic.StageEqualityRows.Naturals

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the actual
row constructor is quadratic in this walk's equality census; its
signed-width factors are separate from the number of walks. -/
theorem raw_budget_quadratic (r : EquationRow.Input) :
    EquationRowRaw.budget r≤10^6*(r.d+r.p+2)^2*(r.cuts.length+1)^2+4*(EquationRowRaw.source r).length := by
  let A:=r.d+r.p+2
  let B:=r.cuts.length+1
  let H:=EquationRowRaw.mass r
  have hA : 1≤A := by dsimp [A];omega
  have hB : 1≤B := by dsimp [B];omega
  have hH : 1≤H := by dsimp [H,EquationRowRaw.mass];omega
  have hd : r.d+1≤H := by dsimp [H,EquationRowRaw.mass];omega
  have hp : r.p+1≤H := by dsimp [H,EquationRowRaw.mass];omega
  have hg : r.cuts.length+1≤H := by dsimp [H,EquationRowRaw.mass];omega
  have bd : natBitLength r.d≤H := (bitLength_le r.d).trans hd
  have bp : natBitLength r.p≤H := (bitLength_le r.p).trans hp
  have bg : natBitLength r.cuts.length≤H := (bitLength_le r.cuts.length).trans hg
  have dd:=EquationRowRaw.dimension_bound r.d (natBitLength r.d) H (by omega) bd hH
  have dp:=EquationRowRaw.dimension_bound r.p (natBitLength r.p) H (by omega) bp hH
  have dg:=EquationRowRaw.dimension_bound r.cuts.length (natBitLength r.cuts.length) H (by omega) bg hH
  have count : EquationCountReady.budget r.d r.p r.cuts.length≤8192*H^2 :=
    EquationCountReady.budget_polynomial r.d r.p r.cuts.length
  have ad:=EquationRowRaw.append_bound r.d H (by omega) hH
  have ap:=EquationRowRaw.append_bound (r.p+1) H (by omega) hH
  have ag:=EquationRowRaw.append_bound (2*r.cuts.length) H (by omega) hH
  have headers : EquationHeaders.budget (EquationHeaderCold.values r.d r.p r.cuts.length)≤1202*H^2 := by
    change EquationHeaderAppend.budget r.d+1+EquationHeaderAppend.budget (r.p+1)+1+
      EquationHeaderAppend.budget (2*r.cuts.length)≤_
    have hsq : 1≤H^2 := Nat.one_le_pow _ _ hH
    omega
  have cap : EquationRowCuts.rowCapacity r≤256*A^2 := by
    calc
      EquationRowCuts.rowCapacity r=128*(2*r.d+1)*(r.p+1) := rfl
      _≤128*(2*A)*A := by gcongr <;> dsimp [A] <;> omega
      _=256*A^2 := by ring
  have eb : EquationRowPhiHeader.eraseBudget r.d r.p≤8*A^2 := by
    unfold EquationRowPhiHeader.eraseBudget EquationRowPhiHeader.driverLength
    dsimp [A]
    nlinarith
  have wb : EquationIdentityColumns.budget r.d≤64*A^2 := by
    unfold EquationIdentityColumns.budget
    dsimp [A]
    nlinarith
  have ha2 : 1≤A^2 := Nat.one_le_pow _ _ hA
  have hab : 1≤A^2*B := Nat.mul_pos ha2 hB
  have hbAB : B≤A^2*B := by simpa using Nat.mul_le_mul_right B ha2
  have loop : EquationRowCuts.budget r.cuts.length (EquationRowCuts.rowCapacity r)≤4102*A^2*B := by
    calc
      EquationRowCuts.budget r.cuts.length (EquationRowCuts.rowCapacity r)≤B*(16*(256*A^2)+3)+3 := by
        unfold EquationRowCuts.budget
        gcongr
        dsimp [B]
        omega
      _=4096*A^2*B+3*B+3 := by ring
      _≤4102*A^2*B := by nlinarith only [hbAB,hab]
  have haAB : A≤A*B := by simpa using Nat.mul_le_mul_left A hB
  have hbAB' : B≤A*B := by simpa using Nat.mul_le_mul_right B hA
  have hHH : H≤2*(A*B) := by
    have h : H≤A+B := by dsimp [H,EquationRowRaw.mass,A,B];omega
    omega
  have hs : H^2≤4*(A^2*B^2) := by
    have h:=Nat.pow_le_pow_left hHH 2
    nlinarith only [h]
  have hAA : A^2≤A^2*B^2 := by
    have hb2 : 1≤B^2 := Nat.one_le_pow _ _ hB
    simpa using Nat.mul_le_mul_left (A^2) hb2
  have hAB : A^2*B≤A^2*B^2 := by
    have hB2 : B≤B^2 := by simpa only [pow_two] using Nat.le_mul_self B
    exact Nat.mul_le_mul_left (A^2) hB2
  have ht : 1≤A^2*B^2 := Nat.mul_pos ha2 (Nat.one_le_pow _ _ hB)
  rw [EquationRowRaw.cost_eq]
  change _≤10^6*A^2*B^2+4*(EquationRowRaw.source r).length
  nlinarith only [dd,dp,dg,count,headers,ad,cap,eb,wb,loop,hs,hAA,hAB,ht]

end NearQuarticWires.StageEqualityRows
