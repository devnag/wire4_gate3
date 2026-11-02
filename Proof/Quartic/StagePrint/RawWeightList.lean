import Proof.Quartic.StagePrint.RawSigned

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.Interfaces (intWord)

/-- `lem:print`, paper/paper.tex: the fixed-width record for one unchanged original coefficient, inside the outer load field. -/
def weightField (W : ℕ) (z : ℤ) : List Bool :=
  (binary W (encS z)).flatMap (layeredBit 2) ++ [true,false]

/-- `lem:print`, paper/paper.tex: one signed coefficient and its record terminator are emitted physically. -/
def readWeight : St VV := .seq (readSignedField 2) (emitL [true,false])

/-- `lem:print` and `prop:time`, paper/paper.tex: all bits of the unchanged original coefficient are charged before any corner translation. -/
theorem readWeight_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (z : ℤ) (rest : List Bool) (W : ℕ)
    (hcw : C.cw.drop a.cp = intWord z ++ rest)
    (hwidth : a.env width = W) (hfit : encS z < 2^C.Wd)
    (hW : W < 2^C.Wd) (hctx : 3 ≤ C.Wd)
    (hinput : C.cw.length+2 ≤ C.Wd) (hlen : C.cw.length+2 < 2^C.Wd) :
    Hs C readWeight a (60*(intWord z).length+30*W+110) (fun b =>
      b.out=a.out++weightField W z ∧ b.cp=a.cp+(intWord z).length ∧
      b.wq=a.wq ∧ b.env width=W ∧ Cst b ∧ Fr a b signedScratch) := by
  unfold readWeight
  refine Hs.mono (Hs.seq (t2:=5) (readSignedField_run C 2 a hc z rest W hcw hwidth
    hfit hW hctx hinput hlen) (fun b ⟨bo,bp,bw,bwidth,bc,bf⟩ => ?_)) (by norm_num;omega)
    (fun _ h => h)
  refine (emitL_spec (C:=C) [true,false] b).mono le_rfl ?_
  rintro e ⟨eo,ep,ew,ef⟩
  have ec : Cst e := Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide),bc.pos,ep])
  exact ⟨by rw [eo,bo];simp [weightField,List.append_assoc],ep.trans bp,ew.trans bw,
    by rw [ef width (by decide)];exact bwidth,ec,
    bf.trans (ef.weaken (by intro y hy;rcases List.mem_singleton.mp hy with rfl;decide))⟩

/-- `lem:print`, paper/paper.tex: the original-weight record cursor. -/
def weightIndex : Fin VV := 125
/-- `lem:print`, paper/paper.tex: the number of original coefficient occurrences, including zero coefficients. -/
def weightCount : Fin VV := 126

/-- `lem:print`, paper/paper.tex: every original coefficient is read once in source order. -/
def readWeights : St VV :=
  .loop (.lt weightIndex weightCount) (.seq readWeight (.op (.inc weightIndex)))

/-- `lem:print`, paper/paper.tex: coefficient serialization changes no unrelated source or dimension register. -/
def weightsScratch : List (Fin VV) := signedScratch ++ [weightIndex]

/-- `lem:print` and `prop:time`, paper/paper.tex: the dense original gate vector is a genuine input scan with explicit output, cursor and polynomial running time. -/
theorem readWeights_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (zs : List ℤ) (rest : List Bool) (W : ℕ)
    (hcw : C.cw.drop a.cp = zs.flatMap intWord ++ rest)
    (hwidth : a.env width=W) (hi : a.env weightIndex=0)
    (hn : a.env weightCount=zs.length)
    (hfit : ∀z∈zs,encS z<2^C.Wd) (hW : W<2^C.Wd)
    (hcount : zs.length<2^C.Wd) (hctx : 3≤C.Wd)
    (hinput : C.cw.length+2≤C.Wd) (hlen : C.cw.length+2<2^C.Wd) :
    Hs C readWeights a (zs.length*(60*C.cw.length+30*W+114)+2) (fun b =>
      b.out=a.out++zs.flatMap (weightField W) ∧
      b.cp=a.cp+(zs.flatMap intWord).length ∧ b.wq=a.wq ∧
      b.env width=W ∧ b.env weightIndex=zs.length ∧ b.env weightCount=zs.length ∧
      Cst b ∧ Fr a b weightsScratch) := by
  let P : ℕ→DS VV→Prop := fun k b =>
    b.out=a.out++(zs.take k).flatMap (weightField W) ∧ b.wq=a.wq ∧
    b.env width=W ∧ Cst b ∧ Fr a b weightsScratch
  have init : P 0 a := by exact ⟨by simp,rfl,hwidth,hc,Fr.refl _ _⟩
  have run := walk (C:=C) zs intWord weightIndex weightCount (by decide) readWeight P
    (60*C.cw.length+30*W+110) rest ?_ ?_ hcount a init hi hn hcw
  · refine run.mono le_rfl ?_
    rintro b ⟨⟨bo,bw,bwidth,bc,bf⟩,bi,bn,bp⟩
    exact ⟨by simpa using bo,bp,bw,bwidth,bi,bn,bc,bf⟩
  · intro k b v ⟨bo,bw,bwidth,bc,bf⟩
    have sf : Fr b (b.set weightIndex v) [weightIndex] := Fr.set _ _ (by simp)
    exact ⟨bo,bw,by rw [sf width (by decide)];exact bwidth,
      Cst.of_fr bc sf (by decide) (by rw [sf vPOS (by decide)];exact bc.pos),
      bf.trans (sf.weaken (by intro y hy;exact List.mem_append_right _ hy))⟩
  · intro k hk b ⟨bo,bw,bwidth,bc,bf⟩ bi bn bd
    have iz : (intWord zs[k]).length ≤ C.cw.length := by
      have hh := congrArg List.length bd
      simp only [List.length_drop,List.length_append] at hh
      omega
    refine (readWeight_run C b bc zs[k] _ W bd bwidth
      (hfit _ (List.getElem_mem hk)) hW hctx hinput hlen).mono (by omega) ?_
    rintro e ⟨eo,ep,ew,ewidth,ec,ef⟩
    refine ⟨⟨?_,ew.trans bw,ewidth,ec,bf.trans (ef.weaken ?_)⟩,?_,?_,ep⟩
    · rw [eo,bo,List.take_succ_eq_append_getElem hk,List.flatMap_append,List.flatMap_singleton]
      exact List.append_assoc _ _ _
    · intro y hy;exact List.mem_append_left _ hy
    · rw [ef weightIndex (by decide)];exact bi
    · rw [ef weightCount (by decide)];exact bn

end NearQuarticWires.StagePrint.RawBits
