import Proof.Quartic.StageCertNativePoolCost.Aggregate

set_option autoImplicit false

namespace NearQuarticWires.StageCertNativePoolCost

open NearCubicWires
open StageCertNative StageCertificateControl

/-- `prop:time`, paper/paper.tex: the
complete actual signed-source loop, once-cached original context,
binary bootstrap, legacy numeric index writer and final payload scan
fit the existing original-column reserve for every actual per-term clock
of occurrence exponent four. No new runtime input or guard is used. -/
theorem wholeWeak_cost (B1 B2 : ℕ) : WholeWeakCostClaim B1 B2 := by
  intro budget hb
  obtain ⟨C,E,hcharge⟩:=price_jobCharge hb
  refine ⟨10^7*(C+1),E,fun r=>?_⟩
  let A:=C*(r.prepared.call.n+1)^E
  let U:=r.prepared.selected.1.Uocc
  let D:=wholeDegree r
  let R:=2^(r.prepared.call.n-r.prepared.selected.1.k)
  have hj (i : Fin (termCount r)) : jobCharge budget ⟨r,i⟩≤A*U^(4*D) := by
    exact hcharge ⟨r,i⟩
  have hc:=count_fourth_reserve r
  have ht:=count_squared_price_reserve r
  change (termCount r)^4≤R at hc
  change (termCount r)^2*U^(4*D)≤R at ht
  have hN : 1≤(r.prepared.call.n+1)^E:=Nat.one_le_pow _ _ (by omega)
  calc
    _≤10^7*((termCount r)^4+(termCount r)^2*(A*U^(4*D))) := whole_budget_bound budget r _ hj
    _=10^7*((termCount r)^4+A*((termCount r)^2*U^(4*D))) := by ring
    _≤10^7*(R+A*R) := Nat.mul_le_mul_left _ (Nat.add_le_add hc (Nat.mul_le_mul_left _ ht))
    _≤10^7*((C+1)*(r.prepared.call.n+1)^E)*R := by dsimp only [A];nlinarith only [hN]
    _=_ := by ring

end NearQuarticWires.StageCertNativePoolCost
