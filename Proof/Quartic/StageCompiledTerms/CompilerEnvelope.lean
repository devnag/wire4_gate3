import Proof.Quartic.StageCompiledTerms.PacketCompiler
import Proof.Quartic.StageRecovery.SelectedResidueCompiler
import Proof.Quartic.StageLiftSourceCost.Reserve

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the counted
formatter's structural hint equals the literal compiler request's
actual squared syntax bound; there is no alternative Formula codec. -/
theorem modularFamily_eq_literal {V : ℕ} (q D : ℕ) (F : Formula V)
    (hq : 2≤q) (hD : F.degree≤D) :
    StageFormulaMetadata.modularFamily q D F hq hD=
      StageRecovery.literalCompileRequest (StageLift.reduceConstants q F) q hq D
        (by rwa [StageLift.reduceConstants_degree]) := by
  unfold StageFormulaMetadata.modularFamily StageRecovery.literalCompileRequest
  simp only [StageFormulaMetadata.countedHint_toks]

/-- `prop:time`, paper/paper.tex: the exact
actual tuple-mask/compiler envelope is independent of walk index,
original target magnitudes and original Gamma values. -/
noncomputable def unitCompilerBound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  let p:=r.child.selected.1
  let D:=StageLift.residueDegreeBound p r.prime
  4*27*10^22*(TSK StageRecovery.packetCallee+10)*
    (StageRecovery.tupleResidueCompilerFactor r.child.call p r.prime D)^6*
      (17*(Builder.allGates r.child.call).length+1)^(2*D+6*p.Xmax+6)

/-- `lem:print` and `prop:time`, paper/paper.tex: the original source packet's actual
normalized tuple AST joins the checked physical compiler cost exactly. -/
theorem walkFamily_budget_le {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    (walkFamily w).modularTermsBudget≤unitCompilerBound w.1 := by
  let r:=w.1
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  let walk:=StageLift.printWalkAt r.child.cellCall.seed.N w.2
  let digits:=fun j row=>r.digits j row%(r.prime^r.child.selected.1.e:ℤ)
  let residues:=fun j=>r.residues j%(r.prime^r.child.selected.1.e:ℤ)
  let weight:=Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign walk
  have heq : walkFamily w=StageRecovery.residueCompileRequest r.child.call hs r.child.witness
      walk r.pattern r.prime r.prime_mem digits residues weight := by
    unfold walkFamily
    rw [modularFamily_eq_literal]
    rfl
  rw [heq]
  exact StageRecovery.residueCompileRequest_budget r.child.call hs r.child.witness walk r.pattern
    r.prime r.prime_mem digits residues weight

/-- `prop:time`, paper/paper.tex: the actual
all-walk compiler census fits the original selected column budget
with the unchanged degree reserve and fixed arity polynomial. -/
theorem unitCompilerBound_selected {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N^8*unitCompilerBound r≤
      StageRecovery.selectedCompilerConstant B1*2^(r.child.call.n-r.child.selected.1.k)*
        (r.child.call.n+1)^StageRecovery.selectedCompilerExponent B1 := by
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hadm:=(Program.dispatch_admitted r.child.dispatched).1
  have hb : 1≤(Builder.callInput r.child.call).beta*((Builder.callInput r.child.call).n:ℚ)^B1 :=
    hadm.2.2.2.2.2.2.2.2.2.1
  have hp : r.prime≤r.child.selected.1.P := by
    have hm:=r.prime_mem
    change r.prime∈r.child.selected.1.primes at hm
    rw [hs.primes_eq,NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1
  have hD:=StageLift.residueDegreeBound_le_Dmax hs r.prime hp
  have hX : 16*r.child.selected.1.Xmax≤StageLift.residueDegreeBound r.child.selected.1 r.prime := by
    unfold StageLift.residueDegreeBound
    omega
  exact (Nat.mul_le_mul_right _ (StageLiftSourceCost.walkCount_le r)).trans
    (StageRecovery.selected_tuple_compiler_envelope r.child.call hs B1 hb r.prime r.prime_mem
      (StageLift.residueDegreeBound r.child.selected.1 r.prime) hD hX)

end NearQuarticWires.StageCompiledTerms
