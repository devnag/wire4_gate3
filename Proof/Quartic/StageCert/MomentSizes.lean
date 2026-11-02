import Proof.Quartic.StageCert.MomentArity
import Proof.Quartic.StageMain.HeaderWidth

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain StageMain.Compact StageLift

/-- `prop:time`, paper/paper.tex: the concrete
shared structural machine has fixed coefficient/exponent reserves,
chosen once independently of the call and proposed witness. -/
noncomputable def momentCalleeCoefficient (B1 B2 : ℕ) : ℕ :=
  Classical.choose (StageMainMask.structuralBudget_arity B1 B2)

noncomputable def momentCalleeExponent (B1 B2 : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (StageMainMask.structuralBudget_arity B1 B2))

/-- `prop:time`, paper/paper.tex: these fixed
reserves bound the actual shared ordinary callee, not an oracle. -/
theorem momentCallee_bound {B1 B2 : ℕ} (r : StageMainMask.StructuralRequest B1 B2) :
    StageMainMask.structuralBudget r ≤ momentCalleeCoefficient B1 B2*
      (r.call.n+1)^momentCalleeExponent B1 B2 :=
  Classical.choose_spec (Classical.choose_spec (StageMainMask.structuralBudget_arity B1 B2)) r

/-- `lem:print` and `prop:time`, paper/paper.tex: the original finite call header alone selects the
complete source workspace and the actual structural callee reserves. -/
noncomputable def momentSourceSizes (B1 B2 : ℕ) : Sz :=
  ⟨momentWorkspaceCoefficient B1,momentWorkspaceExponent B1 B2,
    momentWorkspaceCoefficient B1,momentWorkspaceExponent B1 B2,
    momentCalleeCoefficient B1 B2+1,momentCalleeExponent B1 B2⟩

/-- `lem:print`, paper/paper.tex: later source
fields and computed structural suffixes leave the original arity header
unchanged, including every proposed witness. -/
theorem MomentRequest.source_header {B1 B2 : ℕ} (r : MomentRequest B1 B2) (suffix : List Bool) :
    leadOnes (r.word++suffix)=1+natBitLength r.call.n := by
  rw [MomentRequest.word,prepWord_eq_compact r.dispatched]
  simp only [compactInput,preparedPrefixWord,List.cons_append,List.append_assoc]
  exact taggedCall_header_width r.call _

private theorem original_arity_power (n d : ℕ) :
    (n+1)^d≤2^(d*(1+natBitLength n)) := by
  have hn : n+1≤2^(1+natBitLength n) := by
    have hh := lt_natBitLength n
    have hp := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ))
      (by omega : natBitLength n≤1+natBitLength n)
    omega
  calc
    (n+1)^d≤(2^(1+natBitLength n))^d := Nat.pow_le_pow_left hn _
    _=2^(d*(1+natBitLength n)) := by rw [←pow_mul,Nat.mul_comm]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual leading header pays the complete original
body capacity on either the source or its computed-flag extension. -/
theorem MomentRequest.sizes_width {B1 B2 : ℕ} (r : MomentRequest B1 B2) (suffix : List Bool) :
    r.bodyCapacity≤(momentSourceSizes B1 B2).W (leadOnes (r.word++suffix)) := by
  rw [r.source_header]
  exact r.bodyCapacity_arity.trans (by
    simpa only [momentSourceSizes,Sz.W,Nat.mul_comm] using
      Nat.mul_le_mul_left (momentWorkspaceCoefficient B1)
        (original_arity_power r.call.n (momentWorkspaceExponent B1 B2)))

/-- `prop:time`, paper/paper.tex: every physical
source setup includes the fixed binary parser constants. -/
theorem momentSourceSizes_min (B1 B2 header : ℕ) :
    64≤(momentSourceSizes B1 B2).W header := by
  have hp : 1≤2^(momentWorkspaceExponent B1 B2*header) := Nat.pow_pos (by decide)
  unfold momentSourceSizes Sz.W momentWorkspaceCoefficient
  nlinarith

/-- `def:mask` and `prop:time`, paper/paper.tex: every actual edge request fits the fixed structural
input reserve selected by the original arity header. -/
theorem MomentRequest.sizes_input {B1 B2 : ℕ} (r : MomentRequest B1 B2) (edge : Fin 8) :
    (StageMainMask.structuralWord (r.edgeRequest edge)).length≤
      (momentSourceSizes B1 B2).Lk (leadOnes r.word) := by
  have hs := StageMainMask.structuralWord_length (r.edgeRequest edge)
  change _≤5*(Program.prepWord B1 B2 r.call r.witness).length+2 at hs
  have hp := r.prep_length_le
  have hw : r.word.length≤r.bodyScale := by unfold MomentRequest.bodyScale; omega
  have hS : 2≤r.bodyScale := by unfold MomentRequest.bodyScale; omega
  have hcap : (StageMainMask.structuralWord (r.edgeRequest edge)).length≤r.bodyCapacity := by
    unfold MomentRequest.bodyCapacity
    nlinarith
  have hh := r.sizes_width []
  simp only [List.append_nil] at hh
  exact hcap.trans hh

/-- `def:mask` and `prop:time`, paper/paper.tex: every actual edge call's ordinary computation fits
the once-selected finite work reserve on all original sources. -/
theorem MomentRequest.sizes_callee {B1 B2 : ℕ} (r : MomentRequest B1 B2) (edge : Fin 8) :
    StageMainMask.structuralBudget (r.edgeRequest edge)≤
      (momentSourceSizes B1 B2).Bk (leadOnes r.word) := by
  have hb := momentCallee_bound (r.edgeRequest edge)
  rw [show leadOnes r.word=1+natBitLength r.call.n by
    simpa only [List.append_nil] using r.source_header []]
  dsimp only [MomentRequest.edgeRequest] at hb
  calc
    _ ≤ momentCalleeCoefficient B1 B2*(r.call.n+1)^momentCalleeExponent B1 B2 := hb
    _≤(momentCalleeCoefficient B1 B2+1)*(r.call.n+1)^momentCalleeExponent B1 B2 :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    _≤(momentCalleeCoefficient B1 B2+1)*2^(momentCalleeExponent B1 B2*(1+natBitLength r.call.n)) :=
      Nat.mul_le_mul_left _ (original_arity_power _ _)
    _=_ := by simp only [momentSourceSizes,Sz.Bk,Nat.mul_comm]

end NearQuarticWires.StageCert.Tokens
