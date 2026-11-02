import Proof.Quartic.StageFormulaMetadata.TokenSemantics
import Proof.Quartic.StageFormulaMetadata.FrameRetain
import Proof.Quartic.StageRecovery.ModLoop

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream modulusVar)

/-- `lem:print`, paper/paper.tex: every encoded
token has a nonempty original tag, so its source cursor advances. -/
theorem tokenWord_pos (token : Tok) : 0<(tokWord token).length := by
  rw [tokenWord_eq,List.length_append,natWord_length]
  omega

/-- `lem:print`, paper/paper.tex: the actual
postfix loop stops at the byte count obtained by the frame reader. -/
def metadataLoop (printing : Bool) : St VV MM :=
  .loop (.lt consumedVar payloadLengthVar) (metadataToken printing)

/-- `prop:time`, paper/paper.tex: the loop
charges every actual token scan and its entry/termination tests. -/
def metadataLoopCost (modulus : ℕ) (tokens : List Tok) : ℕ :=
  (tokens.map fun token=>metadataTokenCost modulus token+2).sum+2

/-- `lem:print`, paper/paper.tex: the complete
pass computes its own token, syntax and normalized byte counters. -/
structure TokensPost (printing : Bool) (modulus : ℕ) (tokens : List Tok)
    (a b : DS VV MM) : Prop where
  consumed : b.env consumedVar=a.env consumedVar+(tokenStream tokens).length
  emitted : b.env emittedLengthVar=a.env emittedLengthVar+
    (tokenStream (normalizeTokens modulus tokens)).length
  tokenCount : b.env countedTokensVar=a.env countedTokensVar+tokens.length
  syntaxCount : b.env syntaxSizeVar=a.env syntaxSizeVar+(tokens.map tokenAstSize).sum
  output : b.out=a.out++(if printing then tokenStream (normalizeTokens modulus tokens) else [])
  input : b.ip=a.ip
  memory : b.ram=a.ram
  cursor : b.rc 0=a.rc 0+(tokenStream tokens).length
  otherCursor : ∀ store,store≠0→b.rc store=a.rc store
  callStreams : (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc)
  constants : Cst b
  registers : Fr a b tokenScratch

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal whole-payload pass scans every real
postfix token, computes all counters, and preserves the retained raw
source for the second pass, without a supplied token count. -/
theorem metadataLoop_spec (C : Ctx) (printing : Bool) (tokens : List Tok)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool) (ha : a.ram 0=bits.map Bool.toNat)
    (rest : List Bool) (hin : bits.drop (a.rc 0)=tokenStream tokens++rest)
    (modulus : ℕ) (hq : a.env modulusVar=modulus)
    (hmode : modulus=0 ∨ 2 ≤ modulus) (hmodfit : 2*modulus≤2^C.Wd) (hW : 5≤C.Wd)
    (hfield : ∀ token∈tokens,tokenFieldWidth token+2≤C.Wd)
    (hlimit : a.env payloadLengthVar=a.env consumedVar+(tokenStream tokens).length)
    (hinput : a.env consumedVar+(tokenStream tokens).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(tokenStream (normalizeTokens modulus tokens)).length<2^C.Wd)
    (hcount : a.env countedTokensVar+tokens.length<2^C.Wd)
    (hsize : a.env syntaxSizeVar+(tokens.map tokenAstSize).sum<2^C.Wd) :
    Hs C (metadataLoop printing) a (metadataLoopCost modulus tokens)
      (TokensPost printing modulus tokens a) := by
  induction tokens generalizing a with
  | nil =>
      have he : (Cnd.lt consumedVar payloadLengthVar).eval a=false := by
        simp [Cnd.eval,hlimit,tokenStream]
      refine ⟨a,2,Ex.loopF (show consumedVar≠payloadLengthVar by decide) he,by simp [metadataLoopCost],?_⟩
      exact ⟨by simp [tokenStream],by simp [normalizeTokens,tokenStream],by simp,by simp,
        by simp [normalizeTokens,tokenStream],rfl,rfl,by simp [tokenStream],fun _ _=>rfl,
        rfl,hc,Fr.refl _ _⟩
  | cons token tokens ih =>
      have hraw : tokenStream (token::tokens)=tokWord token++tokenStream tokens := by
        simp only [tokenStream,List.flatMap_cons]
      have hnorm : tokenStream (normalizeTokens modulus (token::tokens))=
          tokWord (normalizeToken modulus token)++tokenStream (normalizeTokens modulus tokens) := by
        simp only [normalizeTokens,List.map_cons,tokenStream,List.flatMap_cons]
      have he : (Cnd.lt consumedVar payloadLengthVar).eval a=true := by
        simp only [Cnd.eval,decide_eq_true_eq]
        rw [hlimit,hraw,List.length_append]
        have hpos:=tokenWord_pos token
        omega
      have eToken:=metadataToken_spec C printing token a hc bits ha (tokenStream tokens++rest)
        (by simpa only [hraw,List.append_assoc] using hin) modulus hq hmode hmodfit hW
        (hfield token (by simp))
        (by rw [hraw,List.length_append] at hinput;omega)
        (by rw [hnorm,List.length_append] at houtput;omega)
        (by simp only [List.length_cons] at hcount;omega)
        (by simp only [List.map_cons,List.sum_cons] at hsize;omega)
      obtain ⟨b,n,eb,hn,hb⟩:=eToken
      have hbinput : bits.drop (b.rc 0)=tokenStream tokens++rest := by
        rw [hb.cursor,←List.drop_drop,hin,hraw,List.append_assoc,List.drop_left]
      have hbq : b.env modulusVar=modulus := by rw [hb.registers _ (by decide),hq]
      have hblimit : b.env payloadLengthVar=b.env consumedVar+(tokenStream tokens).length := by
        rw [hb.registers _ (by decide),hlimit,hb.consumed,hraw,List.length_append]
        omega
      have hbin : b.env consumedVar+(tokenStream tokens).length<2^C.Wd := by
        rw [hb.consumed]
        rw [hraw,List.length_append] at hinput
        omega
      have hbout : b.env emittedLengthVar+(tokenStream (normalizeTokens modulus tokens)).length<2^C.Wd := by
        rw [hb.emitted]
        rw [hnorm,List.length_append] at houtput
        omega
      have hbcnt : b.env countedTokensVar+tokens.length<2^C.Wd := by
        rw [hb.tokens]
        simp only [List.length_cons] at hcount
        omega
      have hbsize : b.env syntaxSizeVar+(tokens.map tokenAstSize).sum<2^C.Wd := by
        rw [hb.syntaxCount]
        simp only [List.map_cons,List.sum_cons] at hsize
        omega
      obtain ⟨last,k,ek,hk,hl⟩:=ih b hb.constants (by rw [hb.memory];exact ha) hbinput hbq
        (fun value hv=>hfield value (by simp [hv])) hblimit hbin hbout hbcnt hbsize
      refine ⟨last,n+k+2,Ex.loopT (show consumedVar≠payloadLengthVar by decide) he eb ek,?_,?_⟩
      · simp only [metadataLoopCost,List.map_cons,List.sum_cons] at hk ⊢
        omega
      · refine ⟨?_,?_,?_,?_,?_,hl.input.trans hb.input,hl.memory.trans hb.memory,
          ?_,?_,hl.callStreams.trans hb.callStreams,hl.constants,hb.registers.trans hl.registers⟩
        · rw [hl.consumed,hb.consumed,hraw,List.length_append]
          omega
        · rw [hl.emitted,hb.emitted,hnorm,List.length_append]
          omega
        · rw [hl.tokenCount,hb.tokens,List.length_cons]
          omega
        · rw [hl.syntaxCount,hb.syntaxCount]
          simp only [List.map_cons,List.sum_cons]
          omega
        · rw [hl.output,hb.output,hnorm]
          cases printing <;> simp only [ite_true,Bool.false_eq_true,ite_false,List.append_nil,List.append_assoc]
        · rw [hl.cursor,hb.cursor,hraw,List.length_append]
          omega
        · intro store hstore
          rw [hl.otherCursor store hstore,hb.otherCursor store hstore]

end NearQuarticWires.StageFormulaMetadata
