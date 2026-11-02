import Proof.Quartic.StageCert.MomentArityBits

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open Cells.ParameterArithmetic

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete literal request includes every threshold
and low-first term-index bit, with no hidden source-height parameter. -/
theorem MomentRequest.source_length_envelope {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.word.length≤(Program.prepWord B1 B2 r.call r.witness).length+
      12*certificateBitEnvelope (preparationEnvelope B1 r.call.n)+
      48*preparationEnvelope B1 r.call.n+3126 := by
  have hb := r.source_bits_envelope
  have h0 := hb (r.test.metadata r.selected.1).tag (by simp [MomentRequest.sourceValues])
  have h1 := hb (r.test.metadata r.selected.1).circuit (by simp [MomentRequest.sourceValues])
  have h2 := hb (r.test.metadata r.selected.1).signOrdinal (by simp [MomentRequest.sourceValues])
  have h3 := hb (r.test.metadata r.selected.1).digitOrdinal (by simp [MomentRequest.sourceValues])
  have h4 := hb (r.test.metadata r.selected.1).threshold (by simp [MomentRequest.sourceValues])
  have h5 := hb r.index.val (by simp [MomentRequest.sourceValues])
  rw [r.word_source_layout]
  simp only [MomentRequest.sourceValues,List.flatMap_cons,List.flatMap_nil,
    List.length_append,List.length_nil,natWord_length]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual source scale is bounded uniformly in all
proposed witness contents by the original selected scalar envelope. -/
theorem MomentRequest.bodyScale_envelope {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.bodyScale≤(Program.prepWord B1 B2 r.call r.witness).length+
      12*certificateBitEnvelope (preparationEnvelope B1 r.call.n)+
      100*preparationEnvelope B1 r.call.n+4000 := by
  let V := preparationEnvelope B1 r.call.n
  have hs := r.scalar_bounds
  have hG : (Builder.allGates r.call).length≤V := by
    have hh := r.rules.occurrences_preparation_envelope B1
    change r.call.first.gates.length+r.call.second.gates.length≤V at hh
    simpa only [Builder.allGates,List.length_append] using hh
  have hn : r.call.n≤V := (Nat.le_succ _).trans (preparation_envelope_arity B1 r.call.n)
  have hlog (v : ℕ) : natBitLength v≤v+1 := by
    unfold natBitLength
    have hh := Nat.log_le_self 2 v
    omega
  have ha : r.atomBits≤17*V+1 := by
    have hh := hlog (17*(Builder.allGates r.call).length)
    change natBitLength (17*(Builder.allGates r.call).length)≤17*V+1
    omega
  have hc : r.coefficientBits≤3*V+2 := by
    have hh := hlog (1+r.call.n+r.selected.1.M1+r.selected.1.A)
    have hm : r.selected.1.M1≤V := hs.M1
    have hA : r.selected.1.A≤V := hs.A
    change natBitLength (1+r.call.n+r.selected.1.M1+r.selected.1.A)≤3*V+2
    omega
  have hsource := r.source_length_envelope
  have hX : r.selected.1.Xmax≤preparationEnvelope B1 r.call.n := hs.Xmax
  have hk : r.selected.1.k≤preparationEnvelope B1 r.call.n := hs.k
  have hJ : r.selected.1.J≤preparationEnvelope B1 r.call.n := hs.J
  have ht : r.selected.1.tau≤preparationEnvelope B1 r.call.n := hs.tau
  dsimp only [MomentRequest.bodyScale]
  dsimp only [V] at hG hn ha hc
  omega

/-- `prop:time`, paper/paper.tex: fixed original
arity powers absorb the literal source, certificate threshold words
and all selected parameter values. -/
def momentScaleExponent (B1 B2 : ℕ) : ℕ :=
  StageMain.Compact.capacityExponent B1 B2+2*(B1+12)+1

def momentScaleCoefficient (B1 : ℕ) : ℕ :=
  StageMain.Compact.capacityCoefficient B1+
    1200*(preparationCoefficient B1+1)^2+100*preparationCoefficient B1+4000

/-- `prop:time`, paper/paper.tex: the actual
workspace scale has a fixed original-arity polynomial bound on all
dispatched calls and every proposed witness. -/
theorem MomentRequest.bodyScale_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.bodyScale ≤ momentScaleCoefficient B1*(r.call.n+1)^momentScaleExponent B1 B2 := by
  let Z := (r.call.n+1)^momentScaleExponent B1 B2
  have hZ : 1≤Z := Nat.pow_pos (Nat.succ_pos _)
  have hp := StageMain.Compact.compactInput_length_arity r.dispatched r.witness
  rw [←StageMain.Compact.prepWord_eq_compact r.dispatched] at hp
  have hprep : (Program.prepWord B1 B2 r.call r.witness).length≤
      StageMain.Compact.capacityCoefficient B1*Z := hp.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (Nat.succ_pos _) (by unfold momentScaleExponent; omega)))
  have hV : preparationEnvelope B1 r.call.n≤preparationCoefficient B1*Z :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
      (by unfold momentScaleExponent; omega))
  have hK : certificateBitEnvelope (preparationEnvelope B1 r.call.n)≤
      100*(preparationCoefficient B1+1)^2*Z :=
    (Cells.certificate_bit_envelope_polynomial B1 r.call.n).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _)
        (by unfold momentScaleExponent; omega)))
  have hconstant : 4000≤4000*Z := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 4000 hZ
  calc
    r.bodyScale≤(Program.prepWord B1 B2 r.call r.witness).length+
      12*certificateBitEnvelope (preparationEnvelope B1 r.call.n)+
        100*preparationEnvelope B1 r.call.n+4000 := r.bodyScale_envelope
    _≤StageMain.Compact.capacityCoefficient B1*Z+
        12*(100*(preparationCoefficient B1+1)^2*Z)+100*(preparationCoefficient B1*Z)+4000*Z := by omega
    _=momentScaleCoefficient B1*Z := by unfold momentScaleCoefficient; ring

/-- `prop:time`, paper/paper.tex: the physical
workspace also includes a fixed minimum for all binary source routines. -/
def momentWorkspaceCoefficient (B1 : ℕ) : ℕ := 100*(momentScaleCoefficient B1)^2+64
def momentWorkspaceExponent (B1 B2 : ℕ) : ℕ := 2*momentScaleExponent B1 B2

/-- `lem:print` and `prop:time`, paper/paper.tex: the concrete full-body binary capacity is paid by one
fixed original-arity polynomial, uniformly before certification. -/
theorem MomentRequest.bodyCapacity_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.bodyCapacity ≤ momentWorkspaceCoefficient B1*(r.call.n+1)^momentWorkspaceExponent B1 B2 := by
  have hh := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left r.bodyScale_arity 2)
  change r.bodyCapacity≤100*(momentScaleCoefficient B1*(r.call.n+1)^momentScaleExponent B1 B2)^2 at hh
  rw [mul_pow,←pow_mul] at hh
  unfold momentWorkspaceCoefficient momentWorkspaceExponent
  calc
    r.bodyCapacity≤100*momentScaleCoefficient B1^2*(r.call.n+1)^(momentScaleExponent B1 B2*2) := by
      simpa only [Nat.mul_assoc] using hh
    _≤(100*momentScaleCoefficient B1^2+64)*(r.call.n+1)^(2*momentScaleExponent B1 B2) := by
      rw [Nat.mul_comm 2 (momentScaleExponent B1 B2)]
      exact Nat.mul_le_mul_right _ (by omega)

end NearQuarticWires.StageCert.Tokens
