import Proof.Quartic.StageCompiledTerms.SourceBytes
import Proof.Quartic.StageCompiledTerms.PacketCompiler
import Proof.Quartic.Control.GammaControl

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageFormulaMetadata

/-- `prop:time`, paper/paper.tex: the marked
formatter's measured finite setup and complete teardown preserve a
constant-factor bound on the original actual formatting clock. -/
theorem framedFormatterBudget_le (request : ValidPacket) :
    framedFormatterBudget request≤5*request.budget := by
  let K:=StageRecovery.packetCallee
  let bits:=request.val.word
  let width:=finiteWidth bits.length
  let A:=500*(width+1)^2+100*(TSK K+3)+5+MM*5*(2*width+1)
  have hlinear : ∀ n,finiteBudget K VV MM bits n=finiteBudget K VV MM bits 0+n*A := by
    intro n
    unfold finiteBudget
    dsimp only [A,width]
    ring
  have hn : 1≤request.steps := by
    dsimp only [ValidPacket.steps,formatterSteps,acquireCost]
    omega
  have hs : 3*request.steps+2≤5*request.steps := by omega
  have hm:=Nat.mul_le_mul_right A hs
  change finiteBudget K VV MM bits (3*request.steps+2)≤5*finiteBudget K VV MM bits request.steps
  rw [hlinear (3*request.steps+2),hlinear request.steps]
  nlinarith

/-- `prop:time`, paper/paper.tex: one uniform
actual source-byte bound contains guarded tuple enumeration and a
fixed original-header polynomial, independently of raw target length. -/
noncomputable def sourcePacketBound {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  7000000000000*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*
    (StageLiftSourceCost.sourceScale r)^30

/-- `prop:time`, paper/paper.tex: the real
literal packet writer supplies the stated uniform positive byte bound. -/
theorem sourcePacketBound_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) :
    (StageLift.sourceWalkPacket r index).word.length + 1 ≤ sourcePacketBound r :=
  source_packet_length_scale r index

/-- `prop:time`, paper/paper.tex: the counted
formatter output has the actual byte-length bound of its physical
writer, so encoded-index projection never uses an unpaid size oracle. -/
theorem indexedWalkFamily_length {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    (indexedWalkFamily w).word.length+1≤
      framedFormatterBudget (StageLift.validSourceWalkPacket w.1 w.2)+1 := by
  have h:=Control.output_length_le framedFormatterWordFunction
    (StageLift.validSourceWalkPacket w.1 w.2)
  rw [StageLift.sourceWalkPacket_formatter_output] at h
  change (frame (indexedWalkFamily w).word).length≤
    framedFormatterBudget (StageLift.validSourceWalkPacket w.1 w.2)+1 at h
  rw [frame_length] at h
  omega

/-- `prop:time`, paper/paper.tex: only the
polynomial raw formatter/projection overhead is squared. The genuine
modular compiler clock remains additive with its sharp family census. -/
theorem packetCompilerBudget_formatting {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    packetCompilerBudget w≤10^50*(sourcePacketBound w.1)^8+
      4*(walkFamily w).modularTermsBudget+100 := by
  let R:=sourcePacketBound w.1
  let F:=framedFormatterBudget (StageLift.validSourceWalkPacket w.1 w.2)
  have hr:=(sourcePacketBound_spec w.1 w.2)
  change (StageLift.sourceWalkPacket w.1 w.2).word.length+1≤R at hr
  have hR : 1≤R := by omega
  have hf:=(framedFormatterBudget_le (StageLift.validSourceWalkPacket w.1 w.2)).trans
    (Nat.mul_le_mul_left 5 (StageLift.sourceWalkPacket_formatter_budget w.1 w.2))
  have hfour:=Nat.pow_le_pow_left hr 4
  have hF : F≤5*10^15*R^4 := by
    change F≤5*(10^15*((StageLift.sourceWalkPacket w.1 w.2).word.length+1)^4) at hf
    nlinarith only [hf,hfour]
  have hP : 1≤R^4:=Nat.pow_pos hR
  have hFF : F+1≤6*10^15*R^4 := by nlinarith only [hF,hP]
  have hFsq:=Nat.pow_le_pow_left hFF 2
  have hprojection:=(Nat.pow_le_pow_left (indexedWalkFamily_length w) 2).trans hFsq
  have hp : (indexedWalkFamily w).word.length.succ^2≤(6*10^15)^2*R^8 := by
    simpa only [mul_pow,←pow_mul] using hprojection
  have h48 : R^4≤R^8:=Nat.pow_le_pow_right hR (by decide)
  have hF8 : F≤5*10^15*R^8:=hF.trans (Nat.mul_le_mul_left _ h48)
  unfold packetCompilerBudget
  change 4*(4*F+4*(10^8*((indexedWalkFamily w).word.length+1)^2)+12)+
    4*(walkFamily w).modularTermsBudget+12≤10^50*R^8+4*(walkFamily w).modularTermsBudget+100
  nlinarith only [hp,hF8]

end NearQuarticWires.StageCompiledTerms
