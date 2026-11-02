import Proof.Quartic.StagePrint.RawWeightEncoding

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: the original dense gate vector is converted directly from its canonical list word to the cold child compiler's first field. -/
def readGateWeights : St VV :=
  .seq readNat (.seq (.op (.copy weightCount t3))
    (.seq (.op (.zero weightIndex)) (.seq readWeights (emitL [true,false,false]))))

/-- `lem:print`, paper/paper.tex: the original dense vector formatter uses only its declared parser, count and bit-writing registers. -/
def gateWeightsScratch : List (Fin VV) := readNatT ++ [weightCount] ++ weightsScratch

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical original-list formatter consumes exactly that list and emits its exact framed fixed-width image. -/
theorem readGateWeights_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (zs : List ℤ) (rest : List Bool) (W : ℕ)
    (hcw : C.cw.drop a.cp=listWord intWord zs++rest)
    (hwidth : a.env width=W) (hfit : ∀z∈zs,encS z<2^C.Wd)
    (hW : W<2^C.Wd) (hcount : zs.length<2^C.Wd)
    (hctx : 3≤C.Wd) (hinput : C.cw.length+2≤C.Wd)
    (hlen : C.cw.length+2<2^C.Wd) :
    Hs C readGateWeights a
      (100*(C.cw.length+2)+(zs.length+1)*(60*C.cw.length+30*W+130))
      (fun b=>b.out=a.out++frame (recStream (zs.map fun z=>
        NearCubicWires.RepairOrdinary.SignedSortKey.binary W (encS z))) ∧
        b.cp=a.cp+(listWord intWord zs).length ∧ b.wq=a.wq ∧
        b.env width=W ∧ b.env weightCount=zs.length ∧ Cst b ∧
        Fr a b gateWeightsScratch) := by
  have hd : C.cw.drop a.cp=natWord zs.length++(zs.flatMap intWord++rest) := by
    simpa only [listWord,List.append_assoc] using hcw
  have hnb : natBitLength zs.length≤C.cw.length := by
    have hh:=congrArg List.length hd
    have hb:=natBitLength_le_len zs.length
    simp only [List.length_drop,List.length_append] at hh
    omega
  unfold readGateWeights
  refine Hx.hs (Hs.then (readNat_spec a hc zs.length _ hd (by omega) hlen)
    (fun b ⟨bv,_,bp,bw,bo,bc,bf⟩ n1 hn1=>?_))
  refine Hs.then (hs_copy C weightCount t3 b (by decide)) (fun e he n2 hn2=>?_)
  subst he
  let e:=b.set weightCount (b.env t3)
  have ef : Fr b e [weightCount] := Fr.set _ _ (by simp)
  have ec : Cst e := Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide)];exact bc.pos)
  refine Hs.then (hs_zero C weightIndex e) (fun f hf n3 hn3=>?_)
  subst hf
  let f:=e.set weightIndex 0
  have ff : Fr e f [weightIndex] := Fr.set _ _ (by simp)
  have fc : Cst f := Cst.of_fr ec ff (by decide)
    (by rw [ff vPOS (by decide)];exact ec.pos)
  have fd : C.cw.drop f.cp=zs.flatMap intWord++rest := by
    change C.cw.drop b.cp=_
    rw [bp,←List.drop_drop,hd,List.drop_left]
  have fw : f.env width=W := by
    rw [ff width (by decide),ef width (by decide),bf width (by decide)]
    exact hwidth
  have fn : f.env weightCount=zs.length := by
    rw [ff weightCount (by decide)]
    simp [e,bv]
  refine Hs.then (readWeights_run C f fc zs rest W fd fw (by simp [f]) fn
    hfit hW hcount hctx hinput hlen) (fun g ⟨go,gp,gw,gwidth,_,gn,gc,gf⟩ n4 hn4=>?_)
  refine Hs.last (emitL_spec (C:=C) [true,false,false] g)
    (fun j ⟨jo,jp,jw,jf⟩ n5 hn5=>?_)
  have jc : Cst j := Cst.of_fr gc jf (by decide)
    (by rw [jf vPOS (by decide),gc.pos,jp])
  refine ⟨⟨?_,?_,?_,?_,?_,jc,?_⟩,?_⟩
  · rw [jo,go]
    simp only [f,e,DS.set_out,bo,List.append_assoc]
    rw [weights_field_eq]
  · rw [jp,gp]
    change b.cp+(zs.flatMap intWord).length=_
    rw [bp,listWord,List.length_append]
    omega
  · simpa only [f,e,DS.set_wq,bw] using jw.trans gw
  · rw [jf width (by decide)];exact gwidth
  · rw [jf weightCount (by decide)];exact gn
  · exact (bf.weaken (by intro y hy;simp only [gateWeightsScratch,List.mem_append];exact Or.inl (Or.inl hy))).trans
      ((ef.weaken (by intro y hy;simp only [gateWeightsScratch,List.mem_append];exact Or.inl (Or.inr hy))).trans
      ((ff.weaken (by intro y hy;simp only [gateWeightsScratch,List.mem_append];exact Or.inr (List.mem_append_right _ hy))).trans
      ((gf.weaken (by intro y hy;simp only [gateWeightsScratch,List.mem_append];exact Or.inr hy)).trans
      (jf.weaken (by intro y hy;rcases List.mem_singleton.mp hy with rfl;decide)))))
  · simp only [List.length_cons,List.length_nil] at hn5
    nlinarith

end NearQuarticWires.StagePrint.RawBits
