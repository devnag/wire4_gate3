import Proof.Quartic.StageCompiledTerms.FormattingBudget
import Proof.Quartic.StageCompiledTerms.CompilerEnvelope
import Proof.Quartic.StageCompiledTerms.Batch
import Proof.Quartic.Cells.ParametersRecoveryReserve

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageLiftSourceCost

/-- `prop:time`, paper/paper.tex: one explicit
per-walk envelope charges the real raw formatter/projection overhead
and the sharp actual modular compiler additively. -/
noncomputable def unitBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  10^50*(sourcePacketBound r)^8+4*unitCompilerBound r+100

/-- `prop:time`, paper/paper.tex: every
actual packet computation obeys the same selected per-walk envelope. -/
theorem packetCompilerBudget_le_unit {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    packetCompilerBudget w≤unitBudget w.1 := by
  have h:=packetCompilerBudget_formatting w
  have hc:=walkFamily_budget_le w
  unfold unitBudget
  omega

/-- `prop:time`, paper/paper.tex: the uniform
byte bound is positive because the actual original walk census is nonempty. -/
theorem sourcePacketBound_pos {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    1 ≤ sourcePacketBound r := by
  have h:=sourcePacketBound_spec r ⟨0,walkCount_pos r⟩
  omega

/-- `prop:time`, paper/paper.tex: real
source bytes are dominated by the explicit actual per-walk clock. -/
theorem sourcePacketBound_le_unit {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    sourcePacketBound r≤unitBudget r := by
  have h:=(Nat.le_self_pow (by decide : (8:ℕ)≠0) (sourcePacketBound r))
  unfold unitBudget
  nlinarith only [h,Nat.zero_le ((sourcePacketBound r)^8)]

/-- `prop:time`, paper/paper.tex: all
one-time small preparation/header routines fit the actual packet-byte
envelope without introducing a following Gamma or raw-index factor. -/
theorem sourcePacketBound_small_overhead {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    10^6*(sourceScale r+1)^3 ≤ sourcePacketBound r := by
  let S:=sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  have hs : 1≤S := by have h:=(sourceScale_small r).1;omega
  have hm : 1≤M:=original_tuple_pos r
  have h30 : S^3≤S^30:=Nat.pow_le_pow_right hs (by decide)
  have hsum:=Nat.pow_le_pow_left (show S+1≤2*S by omega) 3
  have hM:=Nat.mul_le_mul_right (S^30) hm
  change 10^6*(S+1)^3≤7000000000000*M*S^30
  calc 10^6*(S+1)^3≤10^6*(2*S)^3:=Nat.mul_le_mul_left _ hsum
    _=8000000*S^3:=by ring
    _≤8000000*(M*S^30):=Nat.mul_le_mul_left _ (h30.trans (by simpa only [one_mul] using hM))
    _≤7000000000000*(M*S^30):=Nat.mul_le_mul_right _ (by decide)
    _=7000000000000*M*S^30:=by ring

/-- `prop:time`, paper/paper.tex: all raw
formatter/projection syntax powers over the original walk census fit
the existing fifty-degree reserve inside the unchanged guard100. -/
theorem sourcePacketBound_power_reserve {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N^8*(sourcePacketBound r)^8≤
      7000000000000^8*(sourceScale r)^240*2^(r.child.call.n-r.child.selected.1.k) := by
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  let G:=(Builder.allGates r.child.call).length
  let X:=r.child.selected.1.Xmax
  let D:=StageLift.residueDegreeBound r.child.selected.1 r.prime
  have hp : r.prime≤r.child.selected.1.P := by
    have hm:=r.prime_mem
    change r.prime∈r.child.selected.1.primes at hm
    rw [hs.primes_eq,NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1
  have hd : D≤r.child.selected.1.Dmax:=StageLift.residueDegreeBound_le_Dmax hs r.prime hp
  have hX : 16*X≤D := by dsimp only [D,StageLift.residueDegreeBound,X];omega
  have hpool:=StageRecovery.selected_pool_bounds r.child.call hs
  have hocc : G+1≤r.child.selected.1.Uocc := by dsimp only [G];omega
  have hres:=hs.recovery_compiler_reserve G D hocc hd
  have hn:=walkCount_le r
  have hn8 : r.child.cellCall.seed.N^8≤2^(8*r.child.selected.1.k) :=
    hn.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hg : G^(8*X)≤(G+1)^(50*D) :=
    (Nat.pow_le_pow_left (by omega : G≤G+1) _).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hNG : r.child.cellCall.seed.N^8*G^(8*X)≤2^(r.child.call.n-r.child.selected.1.k) :=
    (Nat.mul_le_mul hn8 hg).trans hres
  calc r.child.cellCall.seed.N^8*(sourcePacketBound r)^8=
      (7000000000000^8*(sourceScale r)^240)*(r.child.cellCall.seed.N^8*G^(8*X)) := by
        unfold sourcePacketBound
        simp only [mul_pow,←pow_mul,show r.child.selected.1.Xmax*8=8*X by dsimp [X];omega,
          show 30*8=240 by decide]
        dsimp only [G]
        ring
    _≤_:=Nat.mul_le_mul_left _ hNG

end NearQuarticWires.StageCompiledTerms
