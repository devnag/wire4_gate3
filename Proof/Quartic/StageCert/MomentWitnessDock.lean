import Proof.Quartic.StageCert.MomentRequest
import Proof.Quartic.Program.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens

/-- (W1)–(W3) and `prop:time`, paper/paper.tex: retaining and physically padding the actual witness
prefix preserves every decoded partition and proposed chain bit. -/
theorem MomentRequest.retained_witness_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Builder.witness r.call (p:=r.selected.1) r.retainedWitness=
      Builder.witness r.call (p:=r.selected.1) r.witness := by
  unfold Builder.witness
  apply Program.decodeWitness_congr
  intro m hm
  exact Program.witnessBit_witnessPrefix r.call r.selected.1 r.witness hm

/-- (W2) and `prop:time`, paper/paper.tex: the exact retained zero-padded word preserves the
selection bit of every original repeated occurrence label. -/
theorem MomentRequest.retained_selection_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Builder.selection r.call (p:=r.selected.1) r.retainedWitness=
      Builder.selection r.call (p:=r.selected.1) r.witness := by
  funext i
  unfold Builder.selection
  apply Program.witnessBit_witnessPrefix
  have hlen : (Builder.allGates r.call).length=
      Builder.occurrences r.call 0+Builder.occurrences r.call 1 := by
    simp [Builder.allGates,Builder.occurrences,Builder.gatesOf]
  have hh : (Builder.allGates r.call).length≤
      (r.selected.1.J+1)*(Builder.allGates r.call).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hi := i.isLt
  unfold Program.witnessReadLength
  rw [←hlen]
  omega

/-- (W1) and `prop:time`, paper/paper.tex: the actual center point is unchanged by the finite
source's retained witness representation. -/
theorem MomentRequest.retained_center_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (z : Fin (2^(r.call.n-r.selected.1.k))) :
    Builder.center r.call r.rules r.retainedWitness z=Builder.center r.call r.rules r.witness z := by
  unfold Builder.center Builder.translation
  rw [r.retained_witness_eq]

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: the exact source representation
preserves the complete original column data, including every
failed test and every proposed short or malformed chain. -/
theorem MomentRequest.retained_columnData_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (z : Fin (2^(r.call.n-r.selected.1.k))) :
    Builder.columnData r.call r.rules r.retainedWitness z=
      Builder.columnData r.call r.rules r.witness z := by
  unfold Builder.columnData Builder.contribution Builder.chainBit Builder.center Builder.translation
  rw [r.retained_witness_eq,r.retained_selection_eq]

end NearQuarticWires.StageCert.Tokens
