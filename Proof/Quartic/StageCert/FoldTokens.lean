import Proof.Quartic.StageCert.NewtonToken
import Proof.Quartic.StageCert.TupleMask
import Proof.Quartic.StageCert.RecordAt

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a finite product's postfix stream is its factors, one
literal unit, and one multiplication for each factor. -/
theorem formulaListProd_tokens {V : ℕ} (fs : List (Formula V)) :
    toks (Mask.formulaListProd fs)=fs.flatMap toks++[.const 1]++List.replicate fs.length .mul := by
  induction fs with
  | nil => simp [Mask.formulaListProd,toks]
  | cons f fs ih =>
    simp only [Mask.formulaListProd,toks,ih,List.flatMap_cons,List.length_cons]
    rw [List.replicate_succ']
    simp only [List.append_assoc]

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a finite sum's postfix stream is its summands, one
literal zero, and one addition for each summand. -/
theorem formulaListSum_tokens {V : ℕ} (fs : List (Formula V)) :
    toks (Mask.formulaListSum fs)=fs.flatMap toks++[.const 0]++List.replicate fs.length .add := by
  induction fs with
  | nil => simp [Mask.formulaListSum,toks]
  | cons f fs ih =>
    simp only [Mask.formulaListSum,toks,ih,List.flatMap_cons,List.length_cons]
    rw [List.replicate_succ']
    simp only [List.append_assoc]

namespace Tokens
open NearCubicGates.Close.Cells

/-- `lem:print` and `prop:time`, paper/paper.tex: repeated postfix operators are emitted by a genuine
bounded loop over their actual token count. -/
def emitCopies (token : Tok) : St VV MM :=
  forS sourceRecordIndex sourceRecordLimit (StageLift.emitOperator token)

/-- `lem:print` and `prop:time`, paper/paper.tex: postfix closing operations retain all original coefficient
and source fields, charging every actual operator byte. -/
theorem emitCopies_run (C : Ctx) (token : Tok) (a : DS VV MM) (hc : Cst a)
    (count : ℕ) (hcoun : a.env sourceRecordLimit=count) (hfit : count<2^C.Wd) :
    Hs C (emitCopies token) a (count*(2*(tokWord token).length+5)+4) (fun z=>
      z.out=a.out++(List.replicate count token).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z [sourceRecordIndex,vJ]) := by
  let I : ℕ→DS VV MM→Prop := fun k b=>
    b.out=a.out++(List.replicate k token).flatMap tokWord ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [sourceRecordIndex,vJ]
  have hset : ∀ k b v,I k b→I k (b.set sourceRecordIndex v) := by
    rintro k b v ⟨bo,bs,bc,bfr⟩
    exact ⟨bo,bs,Cst.of_fr (T := [sourceRecordIndex]) bc (Fr.set _ _ (by simp)) (by decide),
      bfr.trans (Fr.set _ _ (by simp))⟩
  unfold emitCopies
  refine (forS_spec' (C := C) sourceRecordIndex sourceRecordLimit (by decide)
    (StageLift.emitOperator token) a count hfit I (2*(tokWord token).length+1) hset
    ⟨by simp,rfl,hc,Fr.refl _ _⟩ hcoun ?_).mono le_rfl ?_
  · intro k hk b ⟨bo,bs,bc,bfr⟩ bi bn
    refine (StageLift.emitOperator_spec C token b bc).mono le_rfl ?_
    rintro z ⟨zo,zs,zc,zfr⟩
    refine ⟨⟨?_,zs.trans bs,zc,bfr.trans (zfr.weaken (by simp))⟩,?_,?_⟩
    · rw [zo,bo,List.replicate_succ',List.flatMap_append,List.flatMap_singleton,List.append_assoc]
    · rw [zfr _ (by decide)]
      exact bi
    · rw [zfr _ (by decide)]
      exact bn
  · rintro z ⟨hz,_,_⟩
    exact hz

end Tokens
end NearQuarticWires.StageCert
