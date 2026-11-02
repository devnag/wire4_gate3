import Proof.Quartic.StagePrint.EntryRetain

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the seven
actual empty fields of the common source context are consumed as
literal delimiter bits, without scanning a following entry. -/
def readEmptyFields : ℕ→St VV MM
  | 0=>skipS
  | count+1=>.seq (.op (.rdI t0)) (readEmptyFields count)

/-- `lem:print`, paper/paper.tex: the exact
finite empty-field parser advances by its literal byte count and
preserves all retained stores and following input. -/
theorem readEmptyFields_run (C : Ctx) (count : ℕ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=List.replicate count false++rest) :
    Hs C (readEmptyFields count) a (2*count+1) (fun b =>
      b.ip=a.ip+count ∧
      (b.out,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.out,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t0,vJ]) := by
  induction count generalizing a with
  | zero=>
    refine (skip_spec (C:=C) a).mono (by simp) ?_
    rintro b rfl
    exact ⟨by simp,rfl,Cst.of_fr hc (Fr.set a _ (T:=[vJ]) (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  | succ count ih=>
    have hin' : C.inp.drop a.ip=[false]++(List.replicate count false++rest) := by
      simpa only [List.replicate_succ,List.cons_append,List.singleton_append,List.nil_append] using hin
    unfold readEmptyFields
    refine (Hs.seq (t2:=2*count+1)
      (StageLift.readInputBit_spec C t0 a false (List.replicate count false++rest) hin')
      fun d hd => ?_).mono (by omega) (fun _ h=>h)
    subst d
    let d:={a.set t0 0 with ip:=a.ip+1}
    have hdc : Cst d := ⟨by simpa (config:={decide:=true}) [d,DS.set] using hc.z,
      by simpa (config:={decide:=true}) [d,DS.set] using hc.one,
      by simpa (config:={decide:=true}) [d,DS.set] using hc.two⟩
    have hdi : C.inp.drop d.ip=List.replicate count false++rest := by
      change C.inp.drop (a.ip+1)=_
      rw [←List.drop_drop,hin']
      rfl
    refine (ih d hdc hdi).mono le_rfl ?_
    rintro b ⟨bi,br,bc,bfr⟩
    refine ⟨by simpa only [d,Nat.add_assoc,Nat.add_comm 1 count] using bi,br,bc,?_⟩
    exact (Fr.set a 0 (T:=[t0,vJ]) (by simp)).trans bfr

end NearQuarticWires.StagePrint.EntryFormat
