import Proof.Quartic.StageGreedyContext.Request
import Proof.Quartic.StageGreedyContext.Layout
import Proof.Quartic.StageGreedyContext.Finish

/-!
# Physical resources for one context computation and a linear carrier pass

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the
one context call is charged its actual compiled source budget. -/
noncomputable def Request.setupBudget {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  (StagePrintContext.contextProducer B1 B2).1 r.prepared

/-- `prop:time`, paper/paper.tex: preparation
acquisition and the measured arity prefix have a finite scalar cost
independent of every numeric count or following entry index. -/
noncomputable def Request.prefixSteps {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  acquirePrepCost r.prep+9*r.prep.length+readFieldCost r.prepared.call.n+
    (natBitLength r.prepared.call.n+10)*(100*r.prepared.call.n+200)+100

/-- `prop:time`, paper/paper.tex: the
physical counter capacity accommodates the measured carrier bytes,
finite preparation and original arity, and one actual context call. -/
noncomputable def Request.capacity {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  1000*(r.word.length+r.prep.length+r.prepared.call.n+natBitLength r.prepared.call.n+
    r.context.length+r.setupBudget+1)+2^(natBitLength r.prep.length+1)+
      2^(natBitLength r.prepared.call.n+1)

/-- `prop:time`, paper/paper.tex: the
unchanged carrier suffix occupies no more bytes than the actual input. -/
theorem Request.suffix_length_le {B1 B2 : ℕ} (r : Request B1 B2) :
    r.suffix.length≤r.word.length := by
  simp only [Request.word,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: the
finite preparation-byte decoder and its literal copy fit the physical
prefix capacity before any context computation or entry scan. -/
theorem Request.acquire_capacity {B1 B2 : ℕ} (r : Request B1 B2) :
    20*(r.prep.length+1)+2^(natBitLength r.prep.length+1)≤r.capacity := by
  have hp : 0≤(2:ℕ)^natBitLength r.prep.length:=Nat.zero_le _
  have hn : 0≤(2:ℕ)^natBitLength r.prepared.call.n:=Nat.zero_le _
  unfold Request.capacity
  omega

/-- `prop:time`, paper/paper.tex: the
measured preparation counters and original-arity decoder fit the same
physical capacity, independently of the following suffix. -/
theorem Request.arity_capacity {B1 B2 : ℕ} (r : Request B1 B2) :
    3*r.prep.length+20*(r.prepared.call.n+natBitLength r.prepared.call.n+1)+
      2^(natBitLength r.prepared.call.n+1)≤r.capacity := by
  have hp : 0≤(2:ℕ)^natBitLength r.prep.length:=Nat.zero_le _
  have hn : 0≤(2:ℕ)^natBitLength r.prepared.call.n:=Nat.zero_le _
  unfold Request.capacity
  omega

/-- `prop:time`, paper/paper.tex: the
final nested-context frame and complete unchanged suffix fit the
same measured counter capacity, with no carrier-size square. -/
theorem Request.finish_capacity {B1 B2 : ℕ} (r : Request B1 B2) :
    100*(r.context.length+r.suffix.length+1)≤r.capacity := by
  have h:=r.suffix_length_le
  have hp : 0≤(2:ℕ)^natBitLength r.prep.length:=Nat.zero_le _
  have hn : 0≤(2:ℕ)^natBitLength r.prepared.call.n:=Nat.zero_le _
  unfold Request.capacity
  omega

/-- `prop:time`, paper/paper.tex: one
actual context computation and all physical byte passes have a
linear-carrier clock plus finite original-source work. -/
noncomputable def Request.sourceSteps {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  r.prefixSteps+2*r.setupBudget+30*(StagePrint.Context.word r.prepared).length+
    finishContextCost r.context r.suffix+100

end NearQuarticWires.StageGreedyContext
