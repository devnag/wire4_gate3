import Proof.Quartic.StagePrint.RawGateWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: the child compiler's dense-dimension field is written as an actual framed unary word. -/
def unaryFieldLoop : St VV := .loop (.lt weightIndex weightCount)
  (.seq (emitL [true,true]) (.op (.inc weightIndex)))

/-- `lem:print`, paper/paper.tex: framed unary output preserves the source and every original gate field. -/
theorem unaryFieldLoop_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (n : ℕ) (hi : a.env weightIndex=0) (hn : a.env weightCount=n)
    (hfit : n<2^C.Wd) :
    Hs C unaryFieldLoop a (9*n+2) (fun b=>
      b.out=a.out++frameP (List.replicate n true) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      b.env weightIndex=n ∧ Cst b ∧ Fr a b [weightIndex,vJ]) := by
  let I : ℕ→DS VV→Prop:=fun k b=>
    b.out=a.out++frameP (List.replicate k true) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
    b.env weightIndex=k ∧ b.env weightCount=n ∧ Cst b ∧ Fr a b [weightIndex,vJ]
  have init : I 0 a := ⟨by simp,rfl,rfl,hi,hn,hc,Fr.refl _ _⟩
  have rr:=Hs.loopN (C:=C) (c:=.lt weightIndex weightCount)
    (s:=.seq (emitL [true,true]) (.op (.inc weightIndex)))
    (show weightIndex≠weightCount from by decide) I n 7 ?_ ?_ a init
  · refine rr.mono (by omega) ?_
    rintro b ⟨bo,bp,bw,bi,_,bc,bf⟩
    exact ⟨bo,bp,bw,bi,bc,bf⟩
  · intro k hk b ⟨bo,bp,bw,bi,bn,bc,bf⟩
    refine ⟨by simp [Cnd.eval,bi,bn,hk],?_⟩
    refine Hs.mono (Hs.seq (t2:=1) (emitL_spec (C:=C) [true,true] b)
      (fun e ⟨eo,ep,ew,ef⟩=>?_)) (by norm_num) (fun _ h=>h)
    have ei : e.env weightIndex=k := by rw [ef weightIndex (by decide)];exact bi
    have en : e.env weightCount=n := by rw [ef weightCount (by decide)];exact bn
    have ec : Cst e:=Cst.of_fr bc ef (by decide)
      (by rw [ef vPOS (by decide),bc.pos,ep])
    refine (hs_inc C weightIndex e (by rw [ei];omega)).mono le_rfl ?_
    rintro f rfl
    have ff : Fr e (e.set weightIndex (e.env weightIndex+1)) [weightIndex,vJ] := Fr.set _ _ (by simp)
    refine ⟨?_,ep.trans bp,ew.trans bw,?_,?_,?_,?_⟩
    · rw [DS.set_out,eo,bo]
      have hh : frameP (List.replicate (k+1) true)=
          frameP (List.replicate k true)++[true,true] := by
        rw [List.replicate_succ']
        simp only [frameP,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      rw [hh,List.append_assoc]
    · simp [ei]
    · rw [ff weightCount (by decide)];exact en
    · exact Cst.of_fr ec ff (by decide) (by rw [ff vPOS (by decide)];exact ec.pos)
    · exact bf.trans ((ef.weaken (by decide)).trans ff)
  · intro b ⟨_,_,_,bi,bn,_⟩
    simp [Cnd.eval,bi,bn]

/-- `lem:print`, paper/paper.tex: unary-field initialization and its final delimiter are explicit program steps. -/
def emitUnaryField : St VV := .seq (.op (.zero weightIndex))
  (.seq unaryFieldLoop (.op (.emit false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the dense dimension is serialized physically, without an encoded-list oracle. -/
theorem emitUnaryField_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (n : ℕ) (hn : a.env weightCount=n) (hfit : n<2^C.Wd) :
    Hs C emitUnaryField a (9*n+7) (fun b=>
      b.out=a.out++frame (List.replicate n true) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      Cst b ∧ Fr a b [weightIndex,vJ]) := by
  unfold emitUnaryField
  refine Hs.mono (Hs.seq (t2:=9*n+4) (hs_zero C weightIndex a) (fun b hb=>?_)) (by omega)
    (fun _ h=>h)
  subst hb
  have sf : Fr a (a.set weightIndex 0) [weightIndex,vJ] := Fr.set _ _ (by simp)
  have sc : Cst (a.set weightIndex 0):=Cst.of_fr hc sf (by decide)
    (by rw [sf vPOS (by decide)];exact hc.pos)
  refine Hs.seq (t1:=9*n+2) (t2:=1) (unaryFieldLoop_run C _ sc n (by simp)
    (by rw [sf weightCount (by decide)];exact hn) hfit) (fun e ⟨eo,ep,ew,_,ec,ef⟩=>?_)
  refine (hs_emit C false e).mono le_rfl ?_
  rintro f rfl
  exact ⟨by rw [frame_eq_frameP,eo];simp [List.append_assoc],ep,ew,
    ⟨ec.z,ec.one,ec.two,ec.pos⟩,sf.trans ef⟩

end NearQuarticWires.StagePrint.RawBits
