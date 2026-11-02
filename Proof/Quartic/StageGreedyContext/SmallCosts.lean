import Proof.Quartic.StageGreedyContext.Resources
import Proof.Quartic.StagePacket.ProjectionCost
import Proof.Quartic.StageMain.CallSize
import Proof.Quartic.Control.GammaControl

/-!
# Finite-source arithmetic does not multiply the complete carrier length

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyContext

attribute [local irreducible] StagePrintContext.contextProducer

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertTests

/-- `prop:time`, paper/paper.tex: decoding
the finite preparation byte count has a quadratic actual clock in
that preparation length, independent of the arbitrary carrier suffix. -/
theorem acquirePrepCost_bound (prep : List Bool) :
    acquirePrepCost prep≤2000*(prep.length+1)^2 := by
  have h:=StagePacket.payloadLengthCost_bound prep.length
  unfold acquirePrepCost StagePacket.payloadLengthCost at *
  nlinarith

/-- `prop:time`, paper/paper.tex: the
actual finite arity decoder and measured return have quadratic cost
in the original arity, with every scalar instruction included. -/
theorem readFieldCost_bound (n : ℕ) : readFieldCost n≤2000*(n+1)^2 := by
  have h:=StagePacket.payloadLengthCost_bound n
  have hb:=StagePacket.projection_bits_bound n
  unfold readFieldCost StagePacket.payloadLengthCost at *
  nlinarith

/-- `prop:time`, paper/paper.tex: the
literal marked arity writer has quadratic actual scalar cost. -/
theorem arityWriterCost_bound (n : ℕ) :
    (natBitLength n+10)*(100*n+200)≤3000*(n+1)^2 := by
  have hb:=StagePacket.projection_bits_bound n
  have hm:=Nat.mul_le_mul_right (100*n+200) (Nat.add_le_add_right hb 10)
  nlinarith

/-- `prop:time`, paper/paper.tex: all
actual common-context output bytes are paid by that sole compiled
source computation, independently of the arbitrary carrier suffix. -/
theorem context_length_le_budget {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    (StagePrint.Context.word r).length≤(StagePrintContext.contextProducer B1 B2).1 r := by
  have h:=Control.output_length_le (StagePrintContext.contextProducer B1 B2).2 r
  simp only [NearCubicGates.Close.Codec.frame_eq_marks,List.length_append,
    Streaming.marks_length,List.length_singleton] at h
  omega

/-- `prop:time`, paper/paper.tex: the
complete finite-source work consists only of original preparation,
arity and the actual single compiled common-context budget. -/
noncomputable def finiteWork {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  2000*(r.word.length+1)^2+9*r.word.length+2000*(r.call.n+1)^2+
    3000*(r.call.n+1)^2+200*(2*r.call.n+3)+
      232*(StagePrintContext.contextProducer B1 B2).1 r+500

/-- `prop:time`, paper/paper.tex: the
literal complete context program has only one linear suffix term;
all other work belongs to its finite original source. -/
theorem sourceSteps_bound {B1 B2 : ℕ} (r : Request B1 B2) :
    r.sourceSteps≤finiteWork r.prepared+200*r.suffix.length := by
  have ha:=acquirePrepCost_bound r.prep
  have hr:=readFieldCost_bound r.prepared.call.n
  have hw:=arityWriterCost_bound r.prepared.call.n
  have hn:=StageMain.CallSize.natWord_le r.prepared.call.n
  have hc:=context_length_le_budget r.prepared
  simp only [Request.sourceSteps,Request.prefixSteps,finishContextCost,Request.context,
    List.length_append,finiteWork,Request.prep,Request.setupBudget] at *
  nlinarith only [ha,hr,hw,hn,hc]

/-- `prop:time`, paper/paper.tex: the
original arity is polynomial in the actual admitted source word. -/
theorem arity_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial (B1:=B1) (B2:=B2) (fun r=>r.call.n) := by
  refine ⟨1,1,fun r=>?_⟩
  have h:=Cells.dispatched_n_le_callWord r.dispatched
  simpa only [Nat.one_mul,pow_one] using h.trans (Nat.le_succ _)

/-- `prop:time`, paper/paper.tex: every
finite-source term is polynomial in the original call-word length,
uniformly over all witnesses and arbitrary suffixes. -/
theorem finiteWork_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial (B1:=B1) (B2:=B2) finiteWork := by
  have hp:=PreparedPolynomial.inputLength (B1:=B1) (B2:=B2)
  have hn:=arity_polynomial B1 B2
  have hc:=StagePrintContext.contextProducer_polynomial B1 B2
  let c:=fun v=>PreparedPolynomial.const (B1:=B1) (B2:=B2) v
  have h1:=(c 2000).mul ((hp.add (c 1)).pow 2)
  have h2:=(c 9).mul hp
  have h3:=(c 2000).mul ((hn.add (c 1)).pow 2)
  have h4:=(c 3000).mul ((hn.add (c 1)).pow 2)
  have h5:=(c 200).mul (((c 2).mul hn).add (c 3))
  have h6:=(c 232).mul hc
  exact (((((h1.add h2).add h3).add h4).add h5).add h6).add (c 500)


end NearQuarticWires.StageGreedyContext
