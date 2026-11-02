import Proof.Quartic.StageFormulaMetadata.HeaderFields
import Proof.Quartic.StageFormulaMetadata.TokenProgram
import Proof.Quartic.StageFormulaMetadata.BinarySums
import Proof.Quartic.StageFormulaMetadata.HintValues

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open StageRecovery (modulusVar)

/-- `lem:print`, paper/paper.tex: actual field
lengths and the complete formula-byte count have dedicated registers. -/
def formulaLengthVar : Fin VV := 110
def modulusBitsVar : Fin VV := 114
def arityLengthVar : Fin VV := 115
def countLengthVar : Fin VV := 116

/-- `lem:print` and `prop:time`, paper/paper.tex: compute the actual formula codec length and modulus
bit width by binary scans, then add the measured payload length. -/
def headerLengths : St VV MM :=
  .seq (naturalLength rawArityVar)
    (.seq (.op (.copy arityLengthVar fieldBytesVar))
      (.seq (naturalLength countedTokensVar)
        (.seq (.op (.copy countLengthVar fieldBytesVar))
          (.seq (naturalLength modulusVar)
            (.seq (.op (.half fieldBytesVar))
              (.seq (.op (.copy modulusBitsVar fieldBytesVar))
                (sumRegisters formulaLengthVar [arityLengthVar,countLengthVar,emittedLengthVar])))))))

/-- `prop:time`, paper/paper.tex: exact header
length computation prices only actual binary-field scans. -/
theorem headerLengths_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (arity count modulus payloadLength : ℕ)
    (ha : a.env rawArityVar=arity) (hn : a.env countedTokensVar=count)
    (hq : a.env modulusVar=modulus) (hl : a.env emittedLengthVar=payloadLength)
    (hformula : formulaLengthValue arity count payloadLength<2^C.Wd)
    (hmodulus : (natWord modulus).length<2^C.Wd) :
    Hs C headerLengths a (5*(natBitLength arity+natBitLength count+natBitLength modulus)+78)
      (fun b=>b.env formulaLengthVar=formulaLengthValue arity count payloadLength ∧
        b.env modulusBitsVar=natBitLength modulus ∧ b.sh=a.sh ∧ Cst b ∧
        Fr a b [aw0,fieldBytesVar,vJ,arityLengthVar,countLengthVar,modulusBitsVar,formulaLengthVar]) := by
  have hA : (natWord arity).length<2^C.Wd := by unfold formulaLengthValue at hformula;omega
  have hN : (natWord count).length<2^C.Wd := by unfold formulaLengthValue at hformula;omega
  unfold headerLengths
  have eA:=naturalLength_spec C rawArityVar (by decide) a hc (by rwa [ha])
  rw [ha] at eA
  refine (Hs.seq (t2:=5*natBitLength count+5*natBitLength modulus+57) eA
    fun b ⟨hb,hbsh,hbc,hbf⟩=>?_).mono (by omega) (fun _ h=>h)
  refine (Hs.seq (t2:=5*natBitLength count+5*natBitLength modulus+55)
    (hs_copy C arityLengthVar fieldBytesVar b (by decide)) fun d hd=>?_).mono
      (by omega) (fun _ h=>h)
  subst d
  let d:=b.set arityLengthVar (b.env fieldBytesVar)
  have hdf : Fr a d [aw0,fieldBytesVar,vJ,arityLengthVar] :=
    (hbf.weaken (by decide)).trans (Fr.set b _ (by decide))
  have hdc : Cst d := Cst.of_fr hbc (Fr.set b _ (T:=[arityLengthVar]) (by decide)) (by decide)
  have hdn : d.env countedTokensVar=count := by rw [hdf _ (by decide),hn]
  have hdA : d.env arityLengthVar=(natWord arity).length := by simpa only [d,DS.set_env_self] using hb
  have eN:=naturalLength_spec C countedTokensVar (by decide) d hdc (by rwa [hdn])
  rw [hdn] at eN
  refine (Hs.seq (t2:=5*natBitLength modulus+34) eN
    fun e ⟨he,hesh,hec,hef⟩=>?_).mono (by omega) (fun _ h=>h)
  refine (Hs.seq (t2:=5*natBitLength modulus+32)
    (hs_copy C countLengthVar fieldBytesVar e (by decide)) fun f hf=>?_).mono
      (by omega) (fun _ h=>h)
  subst f
  let f:=e.set countLengthVar (e.env fieldBytesVar)
  have hff : Fr a f [aw0,fieldBytesVar,vJ,arityLengthVar,countLengthVar] :=
    (hdf.weaken (by decide)).trans
      ((hef.weaken (by decide)).trans (Fr.set e _ (by decide)))
  have hfc : Cst f := Cst.of_fr hec (Fr.set e _ (T:=[countLengthVar]) (by decide)) (by decide)
  have hfq : f.env modulusVar=modulus := by rw [hff _ (by decide),hq]
  have hfA : f.env arityLengthVar=(natWord arity).length := by
    rw [DS.set_env_ne _ _ (show arityLengthVar≠countLengthVar by decide),hef _ (by decide),hdA]
  have hfN : f.env countLengthVar=(natWord count).length := by simpa only [f,DS.set_env_self] using he
  have eQ:=naturalLength_spec C modulusVar (by decide) f hfc (by rwa [hfq])
  rw [hfq] at eQ
  refine (Hs.seq (t2:=11) eQ fun g ⟨hg,hgsh,hgc,hgf⟩=>?_).mono (by omega) (fun _ h=>h)
  refine Hs.seq (t2:=9) (hs_half C fieldBytesVar g) fun h hh=>?_
  subst h
  let h:=g.set fieldBytesVar (g.env fieldBytesVar/2)
  have hhlen : h.env fieldBytesVar=natBitLength modulus := by
    simp only [h,DS.set_env_self,hg,natWord_length]
    omega
  refine Hs.seq (t2:=7) (hs_copy C modulusBitsVar fieldBytesVar h (by decide)) fun j hj=>?_
  subst j
  let j:=h.set modulusBitsVar (h.env fieldBytesVar)
  have hjq : j.env modulusBitsVar=natBitLength modulus := by simpa only [j,DS.set_env_self] using hhlen
  have hlastfr : Fr f j [aw0,fieldBytesVar,vJ,modulusBitsVar] :=
    (hgf.weaken (by decide)).trans
      ((Fr.set g _ (by decide)).trans (Fr.set h _ (by decide)))
  have hje : j.env emittedLengthVar=payloadLength := by
    rw [hlastfr _ (by decide),hff _ (by decide),hl]
  have hjA : j.env arityLengthVar=(natWord arity).length := by rw [hlastfr _ (by decide),hfA]
  have hjN : j.env countLengthVar=(natWord count).length := by rw [hlastfr _ (by decide),hfN]
  have hjc : Cst j := Cst.of_fr hfc hlastfr (by decide)
  refine (sumRegisters_spec C formulaLengthVar [arityLengthVar,countLengthVar,emittedLengthVar]
    j (by decide) (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      hjA,hjN,hje,Nat.add_zero,formulaLengthValue,Nat.add_assoc] using hformula)).mono le_rfl ?_
  rintro last ⟨hresult,hsh,hfr⟩
  have htotfr : Fr a last [aw0,fieldBytesVar,vJ,arityLengthVar,countLengthVar,modulusBitsVar,formulaLengthVar] :=
    (hff.weaken (by decide)).trans ((hlastfr.weaken (by decide)).trans (hfr.weaken (by decide)))
  refine ⟨?_,by rw [hfr _ (by decide),hjq],?_,Cst.of_fr hjc hfr (by decide),htotfr⟩
  · simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hjA,hjN,hje,
      Nat.add_zero,formulaLengthValue,Nat.add_assoc] using hresult
  · exact hsh.trans (hgsh.trans (hesh.trans hbsh))

end NearQuarticWires.StageFormulaMetadata
