import Proof.Quartic.StageFormulaMetadata.HeaderLengths

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: final hint
values and their multiplication scratch have distinct binary registers. -/
def innerHintVar : Fin VV := 107
def setupHintVar : Fin VV := 108
def tenVar : Fin VV := 111
def hintBaseVar : Fin VV := 112
def squareScratchVar : Fin VV := 113

/-- `prop:time`, paper/paper.tex: the exact
frozen inner and outer hints are computed from actual decoded fields
and measured counters using only fixed lists of binary operations. -/
def hintArithmetic : St VV MM :=
  .seq (sumRegisters tenVar [v2,v2,v2,v2,v2])
    (.seq (sumRegisters hintBaseVar [rawArityVar,syntaxSizeVar,formulaLengthVar,modulusBitsVar,tenVar])
      (.seq (squareRegister hintBaseVar squareScratchVar innerHintVar)
        (.seq (sumRegisters hintBaseVar [rawDegreeVar,rawArityVar,tenVar])
          (.seq (squareRegister hintBaseVar squareScratchVar setupHintVar)
            (.op (.add setupHintVar innerHintVar))))))

/-- `prop:time`, paper/paper.tex: the actual
hint arithmetic establishes precisely the compiler's sufficient
workspace fields in a constant number of bounded binary operations. -/
theorem hintArithmetic_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (degree arity syntaxSize count payloadLength modulus : ℕ)
    (hd : a.env rawDegreeVar=degree) (ha : a.env rawArityVar=arity)
    (hs : a.env syntaxSizeVar=syntaxSize)
    (hL : a.env formulaLengthVar=formulaLengthValue arity count payloadLength)
    (hq : a.env modulusBitsVar=natBitLength modulus)
    (hfit : setupValue degree arity syntaxSize count payloadLength modulus<2^C.Wd) :
    Hs C hintArithmetic a 41 (fun b=>
      b.env innerHintVar=hintValue arity syntaxSize count payloadLength modulus ∧
      b.env setupHintVar=setupValue degree arity syntaxSize count payloadLength modulus ∧
      b.sh=a.sh ∧ Cst b ∧
      Fr a b [tenVar,hintBaseVar,squareScratchVar,innerHintVar,setupHintVar]) := by
  have bounds:=hint_partial_bounds degree arity syntaxSize count payloadLength modulus
  dsimp only at bounds
  have hten : 10<2^C.Wd := lt_of_le_of_lt bounds.2.2.2.2.2.2.2.2 hfit
  have hbase : hintBaseValue arity syntaxSize count payloadLength modulus<2^C.Wd :=
    lt_of_le_of_lt (bounds.2.2.2.1.trans bounds.2.2.2.2.2.1) hfit
  have hinner : hintBaseValue arity syntaxSize count payloadLength modulus^2<2^C.Wd :=
    lt_of_le_of_lt bounds.2.2.2.2.2.1 hfit
  have houter : (degree+arity+10)^2<2^C.Wd := lt_of_le_of_lt bounds.2.2.2.2.2.2.1 hfit
  have houterBase : degree+arity+10<2^C.Wd :=
    lt_of_le_of_lt bounds.2.2.2.2.2.2.2.1 houter
  unfold hintArithmetic
  refine Hs.seq (t2:=29) (sumRegisters_spec C tenVar [v2,v2,v2,v2,v2] a (by decide)
    (by simpa [hc.two] using hten))
    fun b ⟨hb,hbsh,hbf⟩=>?_
  have hbten : b.env tenVar=10 := by
    simpa [hc.two] using hb
  have hbc:=Cst.of_fr hc hbf (by decide)
  have hbfields : ([rawArityVar,syntaxSizeVar,formulaLengthVar,modulusBitsVar,tenVar].map b.env).sum=
      hintBaseValue arity syntaxSize count payloadLength modulus := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      hbf rawArityVar (by decide),hbf syntaxSizeVar (by decide),hbf formulaLengthVar (by decide),
      hbf modulusBitsVar (by decide),hbten,ha,hs,hL,hq,hintBaseValue]
    omega
  refine Hs.seq (t2:=17) (sumRegisters_spec C hintBaseVar
    [rawArityVar,syntaxSizeVar,formulaLengthVar,modulusBitsVar,tenVar] b (by decide)
    (by rw [hbfields];exact hbase)) fun d ⟨hdBase,hdsh,hdf⟩=>?_
  rw [hbfields] at hdBase
  have hdc:=Cst.of_fr hbc hdf (by decide)
  have eSquare:=squareRegister_spec C hintBaseVar squareScratchVar innerHintVar (by decide) d
    (by rw [hdBase];exact hinner)
  rw [hdBase] at eSquare
  refine Hs.seq (t2:=13) eSquare fun e ⟨heHint,hesh,hef⟩=>?_
  have hec:=Cst.of_fr hdc hef (by decide)
  have heten : e.env tenVar=10 := by rw [hef _ (by decide),hdf _ (by decide),hbten]
  have hed : e.env rawDegreeVar=degree := by
    rw [hef _ (by decide),hdf _ (by decide),hbf _ (by decide),hd]
  have hea : e.env rawArityVar=arity := by
    rw [hef _ (by decide),hdf _ (by decide),hbf _ (by decide),ha]
  have heFields : ([rawDegreeVar,rawArityVar,tenVar].map e.env).sum=degree+arity+10 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,heten,hed,hea]
    omega
  refine Hs.seq (t2:=5) (sumRegisters_spec C hintBaseVar [rawDegreeVar,rawArityVar,tenVar]
    e (by decide) (by rw [heFields];exact houterBase)) fun f ⟨hfBase,hfsh,hff⟩=>?_
  rw [heFields] at hfBase
  have hfc:=Cst.of_fr hec hff (by decide)
  have eOuter:=squareRegister_spec C hintBaseVar squareScratchVar setupHintVar (by decide) f
    (by rw [hfBase];exact houter)
  rw [hfBase] at eOuter
  refine Hs.seq (t2:=1) eOuter fun g ⟨hgSetup,hgsh,hgf⟩=>?_
  have hgHint : g.env innerHintVar=hintValue arity syntaxSize count payloadLength modulus := by
    rw [hgf _ (by decide),hff _ (by decide),heHint]
    rfl
  have hgc:=Cst.of_fr hfc hgf (by decide)
  refine (hs_add C setupHintVar innerHintVar g (by decide) (by
    rw [hgSetup,hgHint]
    unfold setupValue at hfit
    omega)).mono le_rfl ?_
  rintro last rfl
  refine ⟨by simpa only [DS.set_env_ne _ _ (show innerHintVar≠setupHintVar by decide)] using hgHint,
    by simp only [DS.set_env_self,hgSetup,hgHint,setupValue];omega,
    hgsh.trans (hfsh.trans (hesh.trans (hdsh.trans hbsh))),
    Cst.of_fr hgc (Fr.set g _ (T:=[setupHintVar]) (by decide)) (by decide),?_⟩
  exact (hbf.weaken (by decide)).trans ((hdf.weaken (by decide)).trans
    ((hef.weaken (by decide)).trans ((hff.weaken (by decide)).trans
      ((hgf.weaken (by decide)).trans (Fr.set g _ (by decide))))))

end NearQuarticWires.StageFormulaMetadata
