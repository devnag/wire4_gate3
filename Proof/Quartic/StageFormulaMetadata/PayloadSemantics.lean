import Proof.Quartic.StageFormulaMetadata.ConstantPayload
import Proof.Quartic.StageFormulaMetadata.PowerPayload
import Proof.Quartic.StageFormulaMetadata.TokenView

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery

/-- `lem:print`, paper/paper.tex: all temporary
variables of the shared actual postfix scanner are explicit. -/
def tokenScratch : List (Fin VV) :=
  [tagVar,countedTokensVar,syntaxSizeVar,consumedVar,fieldBytesVar,aw0,emittedLengthVar,
    signVar,leftVar,atomVar,exponentVar,productVar,quotientVar,remainderVar,
    t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ]

/-- `lem:print`, paper/paper.tex: the common
tag handler counts one node; a power payload adds its exponent. -/
def payloadSyntax : Tok→ℕ
  | .pow exponent=>exponent
  | _=>0

/-- `prop:time`, paper/paper.tex: each actual
payload is priced by its decoded binary fields and output fields. -/
def payloadCost (modulus : ℕ) : Tok→ℕ
  | .const value=>30*natBitLength value.natAbs+
      50*natBitLength (normalizedMagnitude modulus value.natAbs (decide (value<0)))+319
  | .var index=>80*natBitLength index+111
  | .pow exponent=>80*natBitLength exponent+113
  | _=>1

/-- `lem:print`, paper/paper.tex: the payload
postcondition records its real input/output bytes, counters and
retained source, including every sign of a constant. -/
structure PayloadPost (printing : Bool) (modulus : ℕ) (token : Tok)
    (a b : DS VV MM) : Prop where
  consumed : b.env consumedVar=a.env consumedVar+(tokenTail token).length
  emitted : b.env emittedLengthVar=a.env emittedLengthVar+
    (tokenTail (normalizeToken modulus token)).length
  tokens : b.env countedTokensVar=a.env countedTokensVar
  syntaxCount : b.env syntaxSizeVar=a.env syntaxSizeVar+payloadSyntax token
  output : b.out=a.out++(if printing then tokenTail (normalizeToken modulus token) else [])
  input : b.ip=a.ip
  memory : b.ram=a.ram
  cursor : b.rc 0=a.rc 0+(tokenTail token).length
  otherCursor : ∀ store,store≠0→b.rc store=a.rc store
  callStreams : (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc)
  constants : Cst b
  registers : Fr a b tokenScratch

/-- `lem:print` and `prop:time`, paper/paper.tex: every one of the seven literal payload handlers has
the same exact source/counter contract, with signed constants and
binary exponent accounting included. -/
theorem metadataPayload_spec (C : Ctx) (printing : Bool) (token : Tok)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool) (ha : a.ram 0=bits.map Bool.toNat)
    (rest : List Bool) (hin : bits.drop (a.rc 0)=tokenTail token++rest)
    (modulus : ℕ) (hq : a.env modulusVar=modulus)
    (hmode : modulus=0 ∨ 2 ≤ modulus) (hmodfit : 2*modulus≤2^C.Wd)
    (hW : 5≤C.Wd) (hfield : tokenFieldWidth token+2≤C.Wd)
    (hinput : a.env consumedVar+(tokenTail token).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(tokenTail (normalizeToken modulus token)).length<2^C.Wd)
    (hsize : a.env syntaxSizeVar+payloadSyntax token<2^C.Wd) :
    Hs C ((metadataHandlers printing)[tokenTag token]'(by
      simpa only [metadataHandlers,List.length_cons,List.length_nil] using tokenTag_lt_seven token))
      a (payloadCost modulus token) (PayloadPost printing modulus token a) := by
  cases token with
  | const value =>
      have e:=constantPayload_spec C printing a hc bits ha value rest hin modulus hq hmode
        hmodfit (by omega) hfield hinput houtput
      refine e.mono le_rfl ?_
      rintro b ⟨hbin,hbout,hbo,hbi,hbr,hbc,hbother,hbcall,hbconst,hbf⟩
      exact ⟨hbin,hbout,hbf _ (by decide),(by
        simpa only [payloadSyntax,Nat.add_zero] using (hbf syntaxSizeVar (by decide))),
        hbo,hbi,hbr,hbc,hbother,hbcall,hbconst,
        hbf.weaken (by decide)⟩
  | var index =>
      have e:=readCountedNatural_spec C printing atomVar (by decide) a hc bits ha index rest
        hin hfield hinput houtput
      refine e.mono le_rfl ?_
      rintro b ⟨_hbv,hbin,hbout,hbo,hbi,hbr,hbc,hbother,hbcall,hbconst,hbf⟩
      exact ⟨hbin,hbout,hbf _ (by decide),(by
        simpa only [payloadSyntax,Nat.add_zero] using (hbf syntaxSizeVar (by decide))),
        hbo,hbi,hbr,hbc,hbother,hbcall,hbconst,
        hbf.weaken (by decide)⟩
  | pow exponent =>
      have e:=powerPayload_spec C printing a hc bits ha exponent rest hin hfield hinput houtput hsize
      refine e.mono le_rfl ?_
      rintro b ⟨hbs,_hbv,hbin,hbout,hbo,hbi,hbr,hbc,hbother,hbcall,hbconst,hbf⟩
      exact ⟨hbin,hbout,hbf _ (by decide),hbs,hbo,hbi,hbr,hbc,hbother,hbcall,hbconst,
        hbf.weaken (by decide)⟩
  | add | neg | sub | mul =>
      refine (skip_spec (C:=C) a).mono le_rfl ?_
      rintro b rfl
      refine ⟨?_,?_,?_,?_,?_,rfl,rfl,?_,fun _ _=>rfl,rfl,?_,?_⟩
      all_goals simp (config:={decide:=true}) [DS.set,tokenTail,normalizeToken,payloadSyntax]
      all_goals first
        | exact Cst.of_fr hc (Fr.set a _ (T:=[vJ]) (by decide)) (by decide)
        | exact Fr.set a _ (by decide)

end NearQuarticWires.StageFormulaMetadata
