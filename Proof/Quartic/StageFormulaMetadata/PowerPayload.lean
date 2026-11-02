import Proof.Quartic.StageFormulaMetadata.TokenProgram

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageRecovery

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual binary exponent is copied and added once
to the syntax counter, with time depending on its bit length. -/
theorem powerPayload_spec (C : Ctx) (printing : Bool) (a : DS VV MM) (hc : Cst a)
    (bits : List Bool) (ha : a.ram 0=bits.map Bool.toNat) (exponent : ℕ) (rest : List Bool)
    (hin : bits.drop (a.rc 0)=natWord exponent++rest)
    (hwidth : natBitLength exponent+2≤C.Wd)
    (hinput : a.env consumedVar+(natWord exponent).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(natWord exponent).length<2^C.Wd)
    (hsize : a.env syntaxSizeVar+exponent<2^C.Wd) :
    Hs C (powerPayload printing) a (80*natBitLength exponent+113) (fun b=>
      b.env syntaxSizeVar=a.env syntaxSizeVar+exponent ∧ b.env exponentVar=exponent ∧
      b.env consumedVar=a.env consumedVar+(natWord exponent).length ∧
      b.env emittedLengthVar=a.env emittedLengthVar+(natWord exponent).length ∧
      b.out=a.out++(if printing then natWord exponent else []) ∧
      b.ip=a.ip ∧ b.ram=a.ram ∧ b.rc 0=a.rc 0+(natWord exponent).length ∧
      (∀ store,store≠0→b.rc store=a.rc store) ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [syntaxSizeVar,exponentVar,consumedVar,fieldBytesVar,aw0,emittedLengthVar,
        t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ]) := by
  unfold powerPayload
  refine (Hs.seq (t2:=1) (readCountedNatural_spec C printing exponentVar (by decide)
    a hc bits ha exponent rest hin hwidth hinput houtput)
    fun b ⟨hbexp,hbin,hbout,hboutput,hbip,hbram,hbrc,hbother,hbrest,hbc,hbf⟩=>?_).mono
      (by omega) (fun _ h=>h)
  have hbsize : b.env syntaxSizeVar=a.env syntaxSizeVar := hbf _ (by decide)
  refine (hs_add C syntaxSizeVar exponentVar b (by decide)
    (by rw [hbsize,hbexp];exact hsize)).mono le_rfl ?_
  rintro d rfl
  refine ⟨by simp only [DS.set_env_self,hbsize,hbexp],?_,?_,?_,hboutput,hbip,hbram,hbrc,
    hbother,hbrest,?_,?_⟩
  · simpa only [DS.set_env_ne _ _ (show exponentVar≠syntaxSizeVar by decide)] using hbexp
  · simpa only [DS.set_env_ne _ _ (show consumedVar≠syntaxSizeVar by decide)] using hbin
  · simpa only [DS.set_env_ne _ _ (show emittedLengthVar≠syntaxSizeVar by decide)] using hbout
  · exact Cst.of_fr hbc (Fr.set b _ (T:=[syntaxSizeVar]) (by decide)) (by decide)
  · exact (hbf.weaken (by decide)).trans (Fr.set b _ (by decide))

end NearQuarticWires.StageFormulaMetadata
