import Proof.Quartic.StagePrint.RawSourceBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (intWord listWord)
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex: the cold original-gate conversion initializes constants, reads its explicit width and scans the unchanged source gate. -/
def coldOriginalGate : St VV := .seq initializeConstants (.seq readNat
  (.seq (.op (.copy width t3)) formatOriginalGate))

/-- `prop:time`, paper/paper.tex: all cold-start, width-header and dense source conversion steps have one explicit budget. -/
def coldOriginalSteps (C : Ctx) (r : OriginalChildRequest) : ℕ :=
  30*natBitLength (r.W+1)+gateFormatterCost C r+50

/-- `lem:print` and `prop:time`, paper/paper.tex: the source-to-original-child subroutine starts on entirely zero registers and produces exactly its full physical child record. -/
theorem coldOriginalGate_run (C : Ctx) (r : OriginalChildRequest)
    (hcw : C.cw=originalGateSource r) (hW : C.cw.length+3≤C.Wd) :
    Hs C coldOriginalGate (a0 (V:=VV)) (coldOriginalSteps C r)
      (fun b=>b.out=r.word) := by
  obtain ⟨hwidth,hcount,hcoeff,htarget⟩:=originalGateSource_bounds r
  rw [←hcw] at hwidth hcount hcoeff htarget
  have hctx : 3≤C.Wd := by omega
  have hlen : C.cw.length+2<2^C.Wd :=
    lt_of_lt_of_le (by omega :C.cw.length+2<C.Wd) (Nat.lt_two_pow_self.le)
  have hfield : r.W+1<2^C.Wd := lt_of_lt_of_le (lt_natBitLength (r.W+1))
    (Nat.pow_le_pow_right (by decide) (hwidth.trans (by omega)))
  have hcnt : r.weights.length<2^C.Wd := lt_of_le_of_lt
    (hcount.trans (by omega :C.cw.length≤C.Wd)) Nat.lt_two_pow_self
  have hcode : ∀z∈r.weights,NearCubicGates.Close.WordPrograms.SInt.encS z<2^C.Wd := by
    intro z hz
    have h:=signed_code_word_bound z C.cw.length (hcoeff z hz)
    have hp:=Nat.pow_le_pow_right (by decide :1≤(2:ℕ)) hW
    omega
  have htarget' : NearCubicGates.Close.WordPrograms.SInt.encS (r.target+1)+3<2^C.Wd :=
    lt_of_lt_of_le (signed_code_word_bound _ _ htarget)
      (Nat.pow_le_pow_right (by decide) hW)
  unfold coldOriginalGate
  refine Hx.hs (Hs.then (initialize_run C hctx)
    (fun a ⟨ac,ap,_,ao,_⟩ n1 hn1=>?_))
  have hd : C.cw.drop a.cp=natWord (r.W+1)++
      (listWord intWord r.weights++intWord (r.target+1)) := by
    rw [ap,List.drop_zero,hcw,originalGateSource,List.append_assoc]
  refine Hs.then (readNat_spec a ac (r.W+1) _ hd (by omega) hlen)
    (fun b ⟨bv,_,bp,_,bo,bc,_⟩ n2 hn2=>?_)
  refine Hs.then (hs_copy C width t3 b (by decide)) (fun e he n3 hn3=>?_)
  subst he
  let e:=b.set width (b.env t3)
  have ef : Fr b e [width] := Fr.set _ _ (by simp)
  have ec : Cst e:=Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide)];exact bc.pos)
  have ed : C.cw.drop e.cp=listWord intWord r.weights++intWord (r.target+1)++[] := by
    change C.cw.drop b.cp=_
    rw [bp,←List.drop_drop,hd,List.drop_left,List.append_nil]
  refine Hs.last (formatOriginalGate_run C e ec r [] ed (by simp [e,bv])
    hcode htarget' hfield hcnt hctx (by omega) hlen)
    (fun f ⟨fo,_⟩ n4 hn4=>?_)
  refine ⟨?_,?_⟩
  · simpa only [e,DS.set_out,bo,ao,List.nil_append] using fo
  · unfold coldOriginalSteps
    omega

end NearQuarticWires.StagePrint.RawBits
