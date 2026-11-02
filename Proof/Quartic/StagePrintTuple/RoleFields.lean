import Proof.Quartic.StagePrint.BaseHeaderEmit
import Proof.Quartic.StagePrint.ReadAtomRole
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StagePrint.Header

/-- `lem:print`, paper/paper.tex:
the two actual occurrence-bank sizes are stored separately until their
sum is used to decode one original polynomial atom. -/
def firstBankCount : Fin VV := 105
def secondBankCount : Fin VV := 106

/-- `lem:print`, paper/paper.tex:
one row-role packet contains the seven actual affine scalars, the two
bank counts, the canonical radix and walk address, and one atom code. -/
structure RolePacket where
  scalars : Fin 7 → ℕ
  firstCount : ℕ
  secondCount : ℕ
  radix : ℕ
  address : ℕ
  atom : Fin (17 * (firstCount + secondCount))

/-- `lem:print`, paper/paper.tex:
the role parser uses only the literal fixed scalar-header destinations. -/
def roleFields : List (Fin VV) :=
  baseHeaderRegisters ++ [firstBankCount,secondBankCount,WalkDigits.radix,
    WalkDigits.number,atomValue]

/-- `lem:print`, paper/paper.tex:
the actual packet values are in the same order as the retained source
context, with its selected atom appended as an ordinary natural word. -/
def RolePacket.values (r : RolePacket) : List ℕ :=
  List.ofFn r.scalars ++ [r.firstCount,r.secondCount,r.radix,r.address,r.atom.val]

/-- `lem:print`, paper/paper.tex:
the row-role input contains only actual scalar codecs, with no decoded
role, original occurrence or selected walk coordinate. -/
def RolePacket.word (r : RolePacket) : List Bool := r.values.flatMap natWord

/-- `lem:print`, paper/paper.tex:
every literal row-role field is physically read from its source bytes. -/
def readRoleFields : St VV MM := StageGamma.readFields roleFields

/-- `lem:print` and `prop:time`, paper/paper.tex: the parser consumes exactly the actual packet
and preserves all source stores, output and call streams. -/
theorem readRoleFields_spec (C : Ctx) (r : RolePacket) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = r.word ++ rest)
    (hwidth : ∀ v ∈ r.values, natBitLength v + 2 ≤ C.Wd) :
    Hs C readRoleFields a (StageGamma.readFieldsCost r.values) (fun b =>
      (∀ j : Fin 7, b.env (baseHeaderRegisters[j.val]'(by
        simp [baseHeaderRegisters])) = r.scalars j) ∧
      b.env firstBankCount = r.firstCount ∧ b.env secondBankCount = r.secondCount ∧
      b.env WalkDigits.radix = r.radix ∧ b.env WalkDigits.number = r.address ∧
      b.env atomValue = r.atom.val ∧ b.ip = a.ip + r.word.length ∧
      (b.out,b.ram,b.rc,b.kin,b.kout,b.kc) =
        (a.out,a.ram,a.rc,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b (roleFields ++ vJ :: rdNatT)) := by
  refine (StageGamma.readFields_spec C roleFields (by decide) (by decide)
    r.values (by simp [roleFields,RolePacket.values,baseHeaderRegisters]) a hc rest
    hin hwidth).mono le_rfl ?_
  rintro b ⟨hv,hi,hr,hbc,hfr⟩
  refine ⟨?_,?_,?_,?_,?_,?_,hi,hr,hbc,hfr⟩
  · intro j
    have hj := hv ⟨j.val,by have := j.isLt; simp [roleFields,baseHeaderRegisters]; omega⟩
    fin_cases j <;> simpa [roleFields,RolePacket.values,baseHeaderRegisters] using hj
  · simpa [roleFields,RolePacket.values,baseHeaderRegisters] using hv ⟨7,by decide⟩
  · simpa [roleFields,RolePacket.values,baseHeaderRegisters] using hv ⟨8,by decide⟩
  · simpa [roleFields,RolePacket.values,baseHeaderRegisters] using hv ⟨9,by decide⟩
  · simpa [roleFields,RolePacket.values,baseHeaderRegisters] using hv ⟨10,by decide⟩
  · simpa [roleFields,RolePacket.values,baseHeaderRegisters] using hv ⟨11,by decide⟩

end NearQuarticWires.StageTuple
