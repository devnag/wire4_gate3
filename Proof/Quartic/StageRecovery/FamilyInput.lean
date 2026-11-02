import Proof.Gates.Expand.Fam4
import Proof.Quartic.StagePrint.UnaryRegister
import Proof.Wire_3_5.CompilerMachineTopLoad
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand
open NearCubicGates.Close.Expand.PolyTab (idealStart)

/-- `lem:print`, paper/paper.tex: the finite Boolean
support family is determined by its original arity and degree bound. -/
structure FamilyRequest where
  arity : ℕ
  degree : ℕ

/-- `lem:print`, paper/paper.tex: family records pack a
characteristic number and its degree using a finite binary width. -/
def FamilyRequest.width (r : FamilyRequest) : ℕ := r.arity + r.degree + 8

/-- `lem:print`, paper/paper.tex: the literal eleven
small family-setup fields contain no precomputed family or point values. -/
def FamilyRequest.fields (r : FamilyRequest) : Fin 11 → List Bool :=
  ![frame (binary r.width 0), frame (binary r.width 0), frame (binary r.width 0),
    frame (binary r.width 1), frame (binary r.width (2 ^ r.arity)),
    frame (binary r.width 0), frame (binary r.width (2 ^ r.arity - 1)),
    List.replicate r.arity true, List.replicate r.degree true, [], []]

/-- `lem:print`, paper/paper.tex: the actual family
constructor input uses the existing finite-field loader record codec. -/
def FamilyRequest.word (r : FamilyRequest) : List Bool :=
  Top.loadRec (r.fields 0) (r.fields 1) (r.fields 2) (r.fields 3) (r.fields 4) (r.fields 5)
    (r.fields 6) (r.fields 7) (r.fields 8) (r.fields 9) (r.fields 10)

/-- `prop:time`, paper/paper.tex: every original family
setup field and marker is paid in the literal loader clock. -/
def FamilyRequest.loadCost (r : FamilyRequest) : ℕ :=
  Top.loadCost (r.fields 0) (r.fields 1) (r.fields 2) (r.fields 3) (r.fields 4) (r.fields 5)
    (r.fields 6) (r.fields 7) (r.fields 8) (r.fields 9) (r.fields 10)

/-- `prop:time`, paper/paper.tex: the family loader's
blank workspace includes every actually serialized setup field. -/
def FamilyRequest.loadCapacity (r : FamilyRequest) : ℕ :=
  2 * r.word.length + 1 +
    Top.loadChainCost (r.fields 0) (r.fields 1) (r.fields 2) (r.fields 3) (r.fields 4) (r.fields 5)
      (r.fields 6) (r.fields 7) (r.fields 8) (r.fields 9) (r.fields 10)

/-- `lem:print`, paper/paper.tex: the family constructor
has distinct work, current-level, next-level and output streams. -/
def familyStreams : Fin 12 ↪ Fin 17 := ⟨![11, 12, 14, 15, 2, 3, 4, 5, 6, 7, 8, 16], by decide⟩

/-- `lem:print`, paper/paper.tex: the original family
constructor registers do not alias the dimension-reader scratch register. -/
def familyRegisters : Fin 14 ↪ Fin 15 :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩, by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)⟩

/-- `lem:print`, paper/paper.tex: the actual loader
bank is a distinct prefix of the complete family-constructor bank. -/
def familyLoadMap (i : Fin 14) : Fin 17 := ⟨i.val, by have := i.isLt; omega⟩

/-- `lem:print`, paper/paper.tex: every loaded field is
on its original named physical stream; other family streams start empty. -/
def FamilyRequest.loaded (r : FamilyRequest) : WState 16 15 :=
  ⟨fun _ => 0, fun i => if h : i.val < 14 then
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, r.word, r.fields 0, r.fields 1, r.fields 2, r.fields 3,
        r.fields 4, r.fields 5, r.fields 6, r.fields 7, r.fields 8, r.fields 9, r.fields 10]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) ⟨i.val, h⟩
    else [], fun _ => 0, false⟩

/-- `lem:print`, paper/paper.tex: unary arity and degree
fields are read before running the actual finite support recurrence. -/
def FamilyRequest.ready (r : FamilyRequest) : WState 16 15 :=
  (r.loaded.setv 10 r.arity).setv 8 r.degree

/-- `lem:print`, paper/paper.tex: the literal loaded
fields meet every start condition of the finite support generator. -/
theorem FamilyRequest.ready_pre (r : FamilyRequest) :
    FS0 familyStreams familyRegisters r.width r.arity r.ready := by
  constructor
  all_goals try rfl
  · simp [FamilyRequest.ready, FamilyRequest.loaded, familyStreams]
  · exact ⟨0, by constructor <;> rfl⟩
  · exact ⟨0, by constructor <;> rfl⟩
  · exact ⟨0, by constructor <;> rfl⟩
  · constructor <;> rfl
  · constructor <;> rfl
  · exact ⟨0, by constructor <;> rfl⟩
  · constructor <;> rfl
  · intro k hk
    fin_cases k <;> simp_all [FamilyRequest.ready, FamilyRequest.loaded, familyRegisters]

end NearQuarticWires.StageRecovery
