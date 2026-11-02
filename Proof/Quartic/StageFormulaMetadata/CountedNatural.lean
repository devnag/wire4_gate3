import Proof.Quartic.StageFormulaMetadata.NaturalLength
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageRecovery (emitVariable emitVariable_spec)

/-- `lem:print`, paper/paper.tex: the normalized
postfix byte count is separate from the actual original source cursor. -/
def emittedLengthVar : Fin VV := 91

/-- `lem:print`, paper/paper.tex: both passes
compute the actual normalized natural-field length; the output pass
also writes the unchanged canonical field to the final output tape. -/
def countedNatural (printing : Bool) (source : Fin VV) : St VV MM :=
  .seq (naturalLength source)
    (.seq (.op (.add emittedLengthVar fieldBytesVar))
      (if printing then emitVariable source else skipS))

/-- `prop:time`, paper/paper.tex: actual field
length and output are obtained by binary scans, with no unary loop
in the numeric magnitude and no assumed normalized byte count. -/
theorem countedNatural_spec (C : Ctx) (printing : Bool) (source : Fin VV)
    (hs : source∉[aw0,fieldBytesVar,emittedLengthVar,t3,t5,t6,t7,t8,t9,vJ])
    (a : DS VV MM) (hc : Cst a) (hW : 2≤C.Wd)
    (hfit : a.env emittedLengthVar+(natWord (a.env source)).length<2^C.Wd) :
    Hs C (countedNatural printing source) a (50*natBitLength (a.env source)+70) (fun b=>
      b.env emittedLengthVar=a.env emittedLengthVar+(natWord (a.env source)).length ∧
      b.out=a.out++(if printing then natWord (a.env source) else []) ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [aw0,fieldBytesVar,emittedLengthVar,t3,t5,t6,t7,t8,t9,vJ]) := by
  have hsNat : source∉[aw0,fieldBytesVar] := by
    intro h
    apply hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have hsSource : source∉[aw0,fieldBytesVar,emittedLengthVar] := by
    intro h
    apply hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have hsEmit : source≠t3 := by intro h;subst source;exact hs (by decide)
  have hlength : (natWord (a.env source)).length<2^C.Wd := by omega
  unfold countedNatural
  refine (Hs.seq (t2:=1+(40*natBitLength (a.env source)+42)+1)
    (naturalLength_spec C source hsNat a hc hlength)
    fun b ⟨hbl,hbsh,hbc,hbf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hbcnt : b.env emittedLengthVar=a.env emittedLengthVar := hbf _ (by decide)
  have hbsrc : b.env source=a.env source := hbf _ (by
    intro h
    apply hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto)
  refine Hs.seq (t2:=40*natBitLength (a.env source)+42)
    (hs_add C emittedLengthVar fieldBytesVar b (by decide) (by rw [hbcnt,hbl];exact hfit))
    fun d hd=>?_
  subst d
  let d:=b.set emittedLengthVar (b.env emittedLengthVar+b.env fieldBytesVar)
  have hdf : Fr a d [aw0,fieldBytesVar,emittedLengthVar,vJ] :=
    (hbf.weaken (by decide)).trans (Fr.set b _ (by decide))
  have hdc : Cst d := Cst.of_fr hbc
    (Fr.set b (b.env emittedLengthVar+b.env fieldBytesVar)
      (x:=emittedLengthVar) (T:=[emittedLengthVar]) (by decide)) (by decide)
  have hdsrc : d.env source=a.env source := by
    rw [hdf source (by
      intro h
      apply hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto)]
  have hdcnt : d.env emittedLengthVar=
      a.env emittedLengthVar+(natWord (a.env source)).length := by simp [d,hbcnt,hbl]
  have hdrest : (d.ip,d.ram,d.rc,d.kin,d.kout,d.kc)=
      (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    change (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=_
    have same:=Same.of_sh hbsh
    rw [same.ip,same.ram,same.rc,same.kin,same.kout,same.kc]
  have hdout : d.out=a.out := (Same.of_sh hbsh).out
  have hbits : natBitLength (d.env source)+2<2^C.Wd := by
    rw [hdsrc]
    have hp:=natBitLength_pos (a.env source)
    rw [natWord_length] at hlength
    omega
  cases printing with
  | false =>
      simp only [Bool.false_eq_true,ite_false]
      refine (skip_spec (C:=C) d).mono (by omega) ?_
      rintro last rfl
      refine ⟨by simpa (config:={decide:=true}) [DS.set] using hdcnt,
        by simpa only [DS.set_out,List.append_nil] using hdout,hdrest,
        Cst.of_fr hdc (Fr.set d _ (T:=[vJ]) (by decide)) (by decide),?_⟩
      exact (hdf.weaken (by decide)).trans (Fr.set d _ (by decide))
  | true =>
      simp only [ite_true]
      have hemit:=emitVariable_spec C d hdc source hsEmit hW hbits
      rw [hdsrc] at hemit
      refine hemit.mono le_rfl ?_
      rintro last ⟨hlo,hlrest,hlc,hlf⟩
      refine ⟨by rw [hlf _ (by decide),hdcnt],by simpa only [hdout] using hlo,
        hlrest.trans hdrest,hlc,(hdf.weaken (by decide)).trans (hlf.weaken (by decide))⟩

end NearQuarticWires.StageFormulaMetadata
