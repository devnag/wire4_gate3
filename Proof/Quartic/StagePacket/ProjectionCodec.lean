import Proof.Quartic.StagePacket.LengthRegisters

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces.Formats
open StagePrint.PacketInterface

/-- `lem:print`, paper/paper.tex: the six actual
indexed fields precede the unchanged exact signed Formula codec. -/
def projectionHeader (r : ExactProjectionRequest) : List ℕ :=
  [r.index,r.setupHint,r.degree,r.payload.length,r.hint,0]

/-- `lem:print`, paper/paper.tex: projection
uses the original header bytes and the original Formula bytes. -/
theorem projection_word (r : ExactProjectionRequest) :
    r.word=(projectionHeader r).flatMap natWord++formulaWord r.formula := by
  simp only [ExactProjectionRequest.word,projectionHeader,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.append_assoc]

/-- `lem:print`, paper/paper.tex: Formula's
literal header consists of arity and the actual postfix token count. -/
theorem projection_formula_word (r : ExactProjectionRequest) :
    formulaWord r.formula=([r.formula.1,(toks r.formula.2).length].flatMap natWord)++r.payload := by
  simp only [formulaWord,NearCubicGates.Close.Interfaces.listWord,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,ExactProjectionRequest.payload,List.append_assoc]

/-- `prop:time`, paper/paper.tex: decoding the
actual byte count requires capacity linear in that consumed payload. -/
theorem projection_power_bound (value : ℕ) : 2^natBitLength value≤2*(value+1) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos value with h | h
  · subst h
    simp
  · have hp:=Nat.pow_log_le_self 2 (show value≠0 by omega)
    rw [pow_succ]
    omega

/-- `prop:time`, paper/paper.tex: every retained
length scratch register is bounded by the actual consumed payload. -/
theorem projection_bits_bound (value : ℕ) : natBitLength value≤value+1 := by
  have hlog:=Nat.log_lt_self 2 (show value+1≠0 by omega)
  have hmono:=Nat.log_mono_right (show value≤value+1 by omega) (b:=2)
  simp only [natBitLength]
  omega

/-- `lem:print`, paper/paper.tex: a skipped
binary field emits no output bytes. -/
theorem projection_empty_map (bits : List Bool) : bits.flatMap (fun _=> ([] : List Bool))=[] := by
  induction bits with
  | nil=>rfl
  | cons bit bits ih=>simpa only [List.flatMap_cons,List.nil_append] using ih

end NearQuarticWires.StagePacket
