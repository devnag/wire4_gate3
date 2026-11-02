import Proof.Quartic.StageFormulaMetadata.HintArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open StageRecovery (modulusVar)

/-- `lem:print`, paper/paper.tex: the emitted
natural fields have exactly the frozen indexed compiler order. -/
def formattedHeaderFields : List (Fin VV) :=
  [rawIndexVar,setupHintVar,rawDegreeVar,emittedLengthVar,innerHintVar,modulusVar,rawArityVar,countedTokensVar]

/-- `lem:print`, paper/paper.tex: every header
byte is physically written from its computed binary register. -/
def emitFormattedHeader : St VV MM := StageCertTests.emitMetadataFields formattedHeaderFields

/-- `prop:time`, paper/paper.tex: binary
register width leaves sufficient room for its own codec bit counter. -/
theorem binaryWidth_room (width : ℕ) (hwidth : 3≤width) : width+2<2^width := by
  have hhalf : width≤2^(width-1) := by
    have h : width-1<2^(width-1) := Nat.lt_two_pow_self
    omega
  have hpow : 2^width=2*2^(width-1) := by
    conv_lhs=>rw [show width=width-1+1 by omega]
    rw [pow_succ]
    omega
  have hmul:=Nat.mul_le_mul_left 2 hhalf
  rw [hpow]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: final header output uses the unchanged natural-field
printer and retains all original source records for the output pass. -/
theorem emitFormattedHeader_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (index setup degree length hint modulus arity count B : ℕ)
    (hi : a.env rawIndexVar=index) (hu : a.env setupHintVar=setup)
    (hd : a.env rawDegreeVar=degree) (hl : a.env emittedLengthVar=length)
    (hh : a.env innerHintVar=hint) (hq : a.env modulusVar=modulus)
    (ha : a.env rawArityVar=arity) (hn : a.env countedTokensVar=count)
    (hB : ∀ field∈formattedHeaderFields,natBitLength (a.env field)≤B)
    (hW : 2≤C.Wd) (hroom : B+2<2^C.Wd) :
    Hs C emitFormattedHeader a (8*(40*B+43)+1) (fun b=>
      b.out=a.out++natWord index++natWord setup++natWord degree++natWord length++
        natWord hint++natWord modulus++natWord arity++natWord count ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t3,t5,t6,t7,t8,t9,vJ]) := by
  have e:=StageCertTests.emitMetadataFields_spec formattedHeaderFields C a hc (by decide) hW
    (fun field hfield=>lt_of_le_of_lt (Nat.add_le_add_right (hB field hfield) 2) hroom)
  refine e.mono ?_ ?_
  · have hsum : (formattedHeaderFields.map fun field=>40*natBitLength (a.env field)+43).sum≤
        8*(40*B+43) := by
      have hbound:=List.sum_le_card_nsmul
        (formattedHeaderFields.map fun field=>40*natBitLength (a.env field)+43) (40*B+43) (by
          intro value hv
          obtain ⟨field,hfield,rfl⟩:=List.mem_map.mp hv
          have h:=hB field hfield
          omega)
      simpa only [List.length_map,formattedHeaderFields,List.length_cons,List.length_nil,smul_eq_mul]
        using hbound
    omega
  · rintro b ⟨hbo,hbrest,hbc,hbf⟩
    refine ⟨?_,hbrest,hbc,hbf⟩
    simpa only [formattedHeaderFields,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
      hi,hu,hd,hl,hh,hq,ha,hn,List.append_nil,List.append_assoc] using hbo

end NearQuarticWires.StageFormulaMetadata
