import Proof.Quartic.StageFormulaMetadata.PayloadSemantics
import Proof.Quartic.StageFormulaMetadata.TokenHead

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats
open StageRecovery

/-- `lem:print`, paper/paper.tex: the actual
tag accounts for one syntax node in every postfix constructor. -/
theorem tokenAstSize_eq (token : Tok) : tokenAstSize token=payloadSyntax token+1 := by
  cases token <;> rfl

/-- `prop:time`, paper/paper.tex: one actual
token pays its field scans and all constant-size tag dispatch tests. -/
def metadataTokenCost (modulus : ℕ) (token : Tok) : ℕ :=
  (80*natBitLength (tokenTag token)+115)+(payloadCost modulus token+3*tokenTag token+1)+1

/-- `lem:print`, paper/paper.tex: one complete
token has exact input/output byte and syntax-counter effects. -/
structure TokenPost (printing : Bool) (modulus : ℕ) (token : Tok)
    (a b : DS VV MM) : Prop where
  consumed : b.env consumedVar=a.env consumedVar+(tokWord token).length
  emitted : b.env emittedLengthVar=a.env emittedLengthVar+(tokWord (normalizeToken modulus token)).length
  tokens : b.env countedTokensVar=a.env countedTokensVar+1
  syntaxCount : b.env syntaxSizeVar=a.env syntaxSizeVar+tokenAstSize token
  output : b.out=a.out++(if printing then tokWord (normalizeToken modulus token) else [])
  input : b.ip=a.ip
  memory : b.ram=a.ram
  cursor : b.rc 0=a.rc 0+(tokWord token).length
  otherCursor : ∀ store,store≠0→b.rc store=a.rc store
  callStreams : (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc)
  constants : Cst b
  registers : Fr a b tokenScratch

/-- `lem:print`, paper/paper.tex: decrementing
the dispatch tag changes no payload counter or source byte. -/
theorem PayloadPost.undoTag {printing : Bool} {modulus : ℕ} {token : Tok}
    {a b : DS VV MM} (h : PayloadPost printing modulus token (a.set tagVar 0) b) :
    PayloadPost printing modulus token a b where
  consumed:=by simpa (config:={decide:=true}) [DS.set] using h.consumed
  emitted:=by simpa (config:={decide:=true}) [DS.set] using h.emitted
  tokens:=by simpa (config:={decide:=true}) [DS.set] using h.tokens
  syntaxCount:=by simpa (config:={decide:=true}) [DS.set] using h.syntaxCount
  output:=h.output
  input:=h.input
  memory:=h.memory
  cursor:=h.cursor
  otherCursor:=h.otherCursor
  callStreams:=h.callStreams
  constants:=h.constants
  registers:=(Fr.set a 0 (x:=tagVar) (by decide)).trans h.registers

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical seven-token scanner computes every
counter and normalized output byte from the original source records. -/
theorem metadataToken_spec (C : Ctx) (printing : Bool) (token : Tok)
    (a : DS VV MM) (hc : Cst a) (bits : List Bool) (ha : a.ram 0=bits.map Bool.toNat)
    (rest : List Bool) (hin : bits.drop (a.rc 0)=tokWord token++rest)
    (modulus : ℕ) (hq : a.env modulusVar=modulus)
    (hmode : modulus=0 ∨ 2 ≤ modulus) (hmodfit : 2*modulus≤2^C.Wd)
    (hW : 5≤C.Wd) (hfield : tokenFieldWidth token+2≤C.Wd)
    (hinput : a.env consumedVar+(tokWord token).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(tokWord (normalizeToken modulus token)).length<2^C.Wd)
    (hcount : a.env countedTokensVar+1<2^C.Wd)
    (hsize : a.env syntaxSizeVar+tokenAstSize token<2^C.Wd) :
    Hs C (metadataToken printing) a (metadataTokenCost modulus token) (TokenPost printing modulus token a) := by
  have htagbits : natBitLength (tokenTag token)+2≤C.Wd := by
    cases token <;> simp only [tokenTag,natBitLength] <;> norm_num <;> omega
  have hlen : (tokWord token).length=(natWord (tokenTag token)).length+(tokenTail token).length := by
    rw [tokenWord_eq,List.length_append]
  have hnlen : (tokWord (normalizeToken modulus token)).length=
      (natWord (tokenTag token)).length+(tokenTail (normalizeToken modulus token)).length := by
    rw [tokenWord_eq,normalizedTag,List.length_append]
  have hsyntax:=tokenAstSize_eq token
  have hhead:=metadataHead_spec C printing a hc bits ha (tokenTag token) _
    (by simpa only [tokenWord_eq,List.append_assoc] using hin) htagbits
    (by rw [hlen] at hinput;omega) (by rw [hnlen] at houtput;omega) hcount
    (by rw [hsyntax] at hsize;omega)
  unfold metadataToken metadataTokenCost
  refine Hs.seq (t2:=payloadCost modulus token+3*tokenTag token+1) hhead
    fun b ⟨hbtag,hbcnt,hbsize,hbcons,hblen,hbout,hbip,hbram,hbrc,hbother,hbcall,hbc,hbf⟩=>?_
  have hbinput : bits.drop (b.rc 0)=tokenTail token++rest := by
    rw [hbrc,←List.drop_drop,hin,tokenWord_eq,List.append_assoc,List.drop_left]
  have hbq : b.env modulusVar=modulus := by rw [hbf _ (by decide),hq]
  let d:=b.set tagVar 0
  have hdc : Cst d := Cst.of_fr hbc (Fr.set b 0 (x:=tagVar) (T:=[tagVar]) (by decide)) (by decide)
  have hdq : d.env modulusVar=modulus := by
    simpa (config:={decide:=true}) [d,DS.set] using hbq
  have hdin : d.env consumedVar+(tokenTail token).length<2^C.Wd := by
    simp only [d,DS.set_env_ne _ _ (show consumedVar≠tagVar by decide)]
    rw [hbcons]
    rw [hlen] at hinput
    omega
  have hdout : d.env emittedLengthVar+(tokenTail (normalizeToken modulus token)).length<2^C.Wd := by
    simp only [d,DS.set_env_ne _ _ (show emittedLengthVar≠tagVar by decide)]
    rw [hblen]
    rw [hnlen] at houtput
    omega
  have hdsize : d.env syntaxSizeVar+payloadSyntax token<2^C.Wd := by
    simp only [d,DS.set_env_ne _ _ (show syntaxSizeVar≠tagVar by decide)]
    rw [hbsize]
    rw [hsyntax] at hsize
    omega
  have eh:=metadataPayload_spec C printing token d hdc bits (by exact hbram ▸ ha) rest
    hbinput modulus hdq hmode hmodfit hW hfield hdin hdout hdsize
  have eh' : Hs C ((metadataHandlers printing)[tokenTag token]'(by
      simpa only [metadataHandlers,List.length_cons,List.length_nil] using tokenTag_lt_seven token))
      d (payloadCost modulus token) (PayloadPost printing modulus token b) :=
    eh.mono le_rfl (fun _ h=>h.undoTag)
  have ed:=tokenDispatch_spec C (metadataHandlers printing) (tokenTag token) (by
      simpa only [metadataHandlers,List.length_cons,List.length_nil] using tokenTag_lt_seven token)
    b hbc hbtag (payloadCost modulus token) (PayloadPost printing modulus token b) eh'
  refine ed.mono le_rfl ?_
  intro last hlast
  refine ⟨?_,?_,by rw [hlast.tokens,hbcnt],?_,?_,hlast.input.trans hbip,
    hlast.memory.trans hbram,?_,?_,hlast.callStreams.trans hbcall,hlast.constants,
    (hbf.weaken (by decide)).trans hlast.registers⟩
  · rw [hlast.consumed,hbcons,hlen]
    omega
  · rw [hlast.emitted,hblen,hnlen]
    omega
  · rw [hlast.syntaxCount,hbsize,hsyntax]
    omega
  · rw [hlast.output,hbout]
    have hnword:=tokenWord_eq (normalizeToken modulus token)
    rw [normalizedTag] at hnword
    cases printing <;> simp only [ite_true,Bool.false_eq_true,ite_false,List.append_nil,
      List.append_assoc,hnword]
  · rw [hlast.cursor,hbrc,hlen]
    omega
  · intro store hstore
    rw [hlast.otherCursor store hstore,hbother store hstore]

end NearQuarticWires.StageFormulaMetadata
