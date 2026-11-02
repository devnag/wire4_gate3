import Proof.Quartic.StageFormulaMetadata.TokenProgram
import Proof.Quartic.StageFormulaMetadata.ConstantCodec

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (intWord)
open StageRecovery StageLift

/-- `lem:print`, paper/paper.tex: the complete
constant token uses only actual signed source fields and the selected
normalization mode, retaining its original finite packet source. -/
theorem constantPayload_spec (C : Ctx) (printing : Bool) (a : DS VV MM) (hc : Cst a)
    (bits : List Bool) (ha : a.ram 0=bits.map Bool.toNat) (value : ℤ) (rest : List Bool)
    (hin : bits.drop (a.rc 0)=intWord value++rest)
    (modulus : ℕ) (hq : a.env modulusVar=modulus)
    (hmode : modulus=0 ∨ 2 ≤ modulus) (hmodfit : 2*modulus≤2^C.Wd)
    (hW : 3≤C.Wd) (hvalue : natBitLength value.natAbs+2≤C.Wd)
    (hinput : a.env consumedVar+(intWord value).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(intWord (value%(modulus:ℤ))).length<2^C.Wd) :
    let negative:=decide (value<0)
    let magnitude:=normalizedMagnitude modulus value.natAbs negative
    Hs C (constantPayload printing) a (30*natBitLength value.natAbs+50*natBitLength magnitude+319)
      (fun b=>
        b.env consumedVar=a.env consumedVar+(intWord value).length ∧
        b.env emittedLengthVar=a.env emittedLengthVar+(intWord (value%(modulus:ℤ))).length ∧
        b.out=a.out++(if printing then intWord (value%(modulus:ℤ)) else []) ∧
        b.ip=a.ip ∧ b.ram=a.ram ∧ b.rc 0=a.rc 0+(intWord value).length ∧
        (∀ store,store≠0→b.rc store=a.rc store) ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
        Fr a b [signVar,leftVar,consumedVar,fieldBytesVar,aw0,emittedLengthVar,
          productVar,quotientVar,remainderVar,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ]) := by
  let negative:=decide (value<0)
  let sign:=negative.toNat
  let magnitude:=normalizedMagnitude modulus value.natAbs negative
  let outsign:=normalizedSign modulus negative
  change Hs C (constantPayload printing) a
    (30*natBitLength value.natAbs+50*natBitLength magnitude+319) _
  have hsignbits : natBitLength sign=1 := by
    dsimp [sign,negative]
    by_cases hv : value<0 <;> simp [hv,natBitLength]
  have hword : intWord value=natWord sign++natWord value.natAbs := integerWord_fields value
  have houtword : intWord (value%(modulus:ℤ))=natWord outsign++natWord magnitude :=
    normalizedInteger_fields modulus value hmode
  have houtsignbits : natBitLength outsign=1 := by
    dsimp [outsign,normalizedSign]
    split
    · cases negative <;> simp [natBitLength]
    · simp [natBitLength]
  have hilen : (intWord value).length=(natWord sign).length+(natWord value.natAbs).length := by
    rw [hword,List.length_append]
  have holen : (intWord (value%(modulus:ℤ))).length=
      (natWord outsign).length+(natWord magnitude).length := by rw [houtword,List.length_append]
  unfold constantPayload
  have eSign:=readTrackedNatural_spec C 0 bits a hc ha signVar (by decide) sign _
    (by simpa only [hword,List.append_assoc] using hin) (by rw [hsignbits];exact hW)
    (by rw [hilen] at hinput;omega)
  rw [hsignbits] at eSign
  refine (Hs.seq (t2:=30*natBitLength value.natAbs+50*natBitLength magnitude+248)
    eSign fun b ⟨hbs,_hbl,hbcons,hbrc,hbrest,hbc,hbf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hbram : b.ram=a.ram := by
    exact congrArg (fun r=>r.2.2.1) hbrest
  have hbq : b.env modulusVar=modulus := by rw [hbf _ (by decide),hq]
  have hboutlen : b.env emittedLengthVar=a.env emittedLengthVar := hbf _ (by decide)
  have hbinput : bits.drop (b.rc 0)=natWord value.natAbs++rest := by
    rw [hbrc,←List.drop_drop,hin,hword,List.append_assoc,List.drop_left]
  have eMagnitude:=readTrackedNatural_spec C 0 bits b hbc (by rw [hbram];exact ha)
    leftVar (by decide) value.natAbs rest hbinput hvalue (by rw [hbcons];rw [hilen] at hinput;omega)
  refine (Hs.seq (t2:=50*natBitLength magnitude+207) eMagnitude
    fun d ⟨hdm,_hdl,hdcons,hdrc,hdrest,hdc,hdf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hdq : d.env modulusVar=modulus := by rw [hdf _ (by decide),hbq]
  have hds : d.env signVar=negative.toNat := by rw [hdf _ (by decide),hbs]
  have hdoutlen : d.env emittedLengthVar=a.env emittedLengthVar := by
    rw [hdf _ (by decide),hboutlen]
  have hdcons' : d.env consumedVar=a.env consumedVar+(intWord value).length := by
    rw [hdcons,hbcons,hilen]
    omega
  have hdrc' : d.rc 0=a.rc 0+(intWord value).length := by
    rw [hdrc,hbrc,hilen]
    omega
  have hreadrest : memorySourceRest 0 d=memorySourceRest 0 a := hdrest.trans hbrest
  simp only [memorySourceRest,Prod.mk.injEq] at hreadrest
  rcases hreadrest with ⟨hdip,hdout,hdram,hdcursor,hdkin,hdkout,hdkc⟩
  have hfields : Fr a d [signVar,leftVar,consumedVar,fieldBytesVar,t0,t1,t2,t3,t4,vJ] :=
    (hbf.weaken (by decide)).trans (hdf.weaken (by decide))
  refine (Hs.seq (t2:=50*natBitLength magnitude+191)
    (normalizeConstant_spec C d hdc modulus value.natAbs negative hdq hdm hds hmode hmodfit)
    fun e ⟨hem,hes,hesh,hec,hef⟩=>?_).mono (by omega) (fun _ h=>h)
  have hesame:=Same.of_sh hesh
  have heoutlen : e.env emittedLengthVar=a.env emittedLengthVar := by
    rw [hef _ (by decide),hdoutlen]
  have hecons : e.env consumedVar=a.env consumedVar+(intWord value).length := by
    rw [hef _ (by decide),hdcons']
  change e.env leftVar=magnitude at hem
  change e.env signVar=outsign at hes
  have ePrintSign:=countedNatural_spec C printing signVar (by decide) e hec (by omega)
    (by rw [hes,heoutlen];rw [holen] at houtput;omega)
  rw [hes,houtsignbits] at ePrintSign
  refine (Hs.seq (t2:=50*natBitLength magnitude+70) ePrintSign
    fun f ⟨hflen,hfout,hfrest,hfc,hff⟩=>?_).mono (by omega) (fun _ h=>h)
  have hfm : f.env leftVar=magnitude := by rw [hff _ (by decide),hem]
  have hflen' : f.env emittedLengthVar=a.env emittedLengthVar+(natWord outsign).length := by
    rw [hflen,heoutlen]
  have ePrintMagnitude:=countedNatural_spec C printing leftVar (by decide) f hfc (by omega)
    (by rw [hfm,hflen'];rw [holen] at houtput;omega)
  rw [hfm] at ePrintMagnitude
  refine ePrintMagnitude.mono le_rfl ?_
  rintro last ⟨hllen,hlo,hlrest,hlc,hlf⟩
  have hffr : Fr d f [leftVar,signVar,productVar,quotientVar,remainderVar,vJ,
      aw0,fieldBytesVar,emittedLengthVar,t3,t5,t6,t7,t8,t9] :=
    (hef.weaken (by decide)).trans (hff.weaken (by decide))
  have hall : Fr a last [signVar,leftVar,consumedVar,fieldBytesVar,aw0,emittedLengthVar,
      productVar,quotientVar,remainderVar,t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ] :=
    (hfields.weaken (by decide)).trans
      ((hffr.weaken (by decide)).trans (hlf.weaken (by decide)))
  simp only [Prod.mk.injEq] at hfrest hlrest
  rcases hfrest with ⟨hfip,hfram,hfrc,hfkin,hfkout,hfkc⟩
  rcases hlrest with ⟨hlip,hlram,hlrc,hlkin,hlkout,hlkc⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hlc,hall⟩
  · rw [hlf _ (by decide),hff _ (by decide),hecons]
  · rw [hllen,hflen',holen]
    omega
  · rw [hlo,hfout,hesame.out,hdout]
    cases printing <;> simp only [ite_true,Bool.false_eq_true,ite_false,List.append_nil,
      List.append_assoc,houtword]
  · rw [hlip,hfip,hesame.ip,hdip]
  · rw [hlram,hfram,hesame.ram,hdram]
  · rw [hlrc,hfrc,hesame.rc,hdrc']
  · intro store hstore
    rw [hlrc,hfrc,hesame.rc]
    have hcursor:=congrFun hdcursor store
    simpa only [Function.update_of_ne hstore] using hcursor
  · rw [hlkin,hlkout,hlkc,hfkin,hfkout,hfkc,hesame.kin,hesame.kout,hesame.kc,
      hdkin,hdkout,hdkc]

end NearQuarticWires.StageFormulaMetadata
