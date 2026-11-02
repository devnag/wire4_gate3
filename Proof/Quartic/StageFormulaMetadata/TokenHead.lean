import Proof.Quartic.StageFormulaMetadata.TokenProgram

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageRecovery

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual tag decoder counts one token and one
syntax node before dispatch, preserving its literal tag value. -/
theorem metadataHead_spec (C : Ctx) (printing : Bool) (a : DS VV MM) (hc : Cst a)
    (bits : List Bool) (ha : a.ram 0=bits.map Bool.toNat) (tag : ℕ) (rest : List Bool)
    (hin : bits.drop (a.rc 0)=natWord tag++rest)
    (hwidth : natBitLength tag+2≤C.Wd)
    (hinput : a.env consumedVar+(natWord tag).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(natWord tag).length<2^C.Wd)
    (hcount : a.env countedTokensVar+1<2^C.Wd)
    (hsize : a.env syntaxSizeVar+1<2^C.Wd) :
    Hs C (metadataHead printing) a (80*natBitLength tag+115) (fun b=>
      b.env tagVar=tag ∧ b.env countedTokensVar=a.env countedTokensVar+1 ∧
      b.env syntaxSizeVar=a.env syntaxSizeVar+1 ∧
      b.env consumedVar=a.env consumedVar+(natWord tag).length ∧
      b.env emittedLengthVar=a.env emittedLengthVar+(natWord tag).length ∧
      b.out=a.out++(if printing then natWord tag else []) ∧
      b.ip=a.ip ∧ b.ram=a.ram ∧ b.rc 0=a.rc 0+(natWord tag).length ∧
      (∀ store,store≠0→b.rc store=a.rc store) ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [tagVar,countedTokensVar,syntaxSizeVar,consumedVar,fieldBytesVar,aw0,emittedLengthVar,
        t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ]) := by
  unfold metadataHead
  refine (Hs.seq (t2:=3) (readCountedNatural_spec C printing tagVar (by decide)
    a hc bits ha tag rest hin hwidth hinput houtput)
    fun b ⟨hbtag,hbin,hbout,hboutput,hbip,hbram,hbrc,hbother,hbrest,hbc,hbf⟩=>?_).mono
      (by omega) (fun _ h=>h)
  have hbcnt : b.env countedTokensVar=a.env countedTokensVar := hbf _ (by decide)
  have hbsize : b.env syntaxSizeVar=a.env syntaxSizeVar := hbf _ (by decide)
  refine Hs.seq (t2:=1) (hs_inc C countedTokensVar b (by rw [hbcnt];exact hcount)) fun d hd=>?_
  subst d
  let d:=b.set countedTokensVar (b.env countedTokensVar+1)
  have hdsize : d.env syntaxSizeVar=a.env syntaxSizeVar := by
    simpa only [d,DS.set_env_ne _ _ (show syntaxSizeVar≠countedTokensVar by decide)] using hbsize
  refine (hs_inc C syntaxSizeVar d (by rw [hdsize];exact hsize)).mono le_rfl ?_
  rintro e rfl
  refine ⟨?_,?_,by simp only [DS.set_env_self,hdsize],?_,?_,hboutput,hbip,hbram,hbrc,
    hbother,hbrest,?_,?_⟩
  · simpa (config:={decide:=true}) [d,DS.set] using hbtag
  · simp (config:={decide:=true}) [d,DS.set,hbcnt]
  · simpa (config:={decide:=true}) [d,DS.set] using hbin
  · simpa (config:={decide:=true}) [d,DS.set] using hbout
  · exact Cst.of_fr hbc
      ((Fr.set b _ (T:=[countedTokensVar,syntaxSizeVar]) (by decide)).trans
        (Fr.set d _ (by decide))) (by decide)
  · exact (hbf.weaken (by decide)).trans
      ((Fr.set b _ (by decide)).trans (Fr.set d _ (by decide)))

end NearQuarticWires.StageFormulaMetadata
