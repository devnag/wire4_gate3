import Proof.Quartic.StageLiftTokens.AmplifierLoop

/-!
# The literal BT sum and final operations

`imp:amp` and `lem:print`, paper/paper.tex: the actual selected exponent controls the trailing addition
count. A final multiplication and subtraction complete the exact
original amplifier syntax after all integer summands have been emitted.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def amplifierTail : St VV MM :=
  .seq (emitOperator (.const 0)) (.seq (.op (.copy sourceRecordLimit degreeExponent))
    (.seq (emitCopies .add) (.seq (emitOperator .mul) (emitOperator .sub))))

def amplifierTailCost (e : ℕ) : ℕ := 20*e+70

theorem amplifierTail_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C amplifierTail a (amplifierTailCost r.child.selected.1.e) (fun b=>
      b.out=a.out++tokWord (.const 0)++(List.replicate r.child.selected.1.e .add).flatMap tokWord++
        tokWord .mul++tokWord .sub ∧ SourceReady C r b E ∧ SourceFrame a b) := by
  have hh : Hs C amplifierTail a (amplifierTailCost r.child.selected.1.e) (fun b=>
      b.out=a.out++tokWord (.const 0)++(List.replicate r.child.selected.1.e .add).flatMap tokWord++
        tokWord .mul++tokWord .sub ∧ SourceFrame a b ∧ Cst b) := by
    unfold amplifierTail
    apply Hx.hs
    refine Hs.then (emitOperator_ready C r a E h (.const 0))
      (fun b ⟨bo,br,bf,_⟩ n1 hn1=>?_)
    refine Hs.then (hs_copy C sourceRecordLimit degreeExponent b (by decide))
      (fun d hd n2 hn2=>?_)
    subst hd
    let d := b.set sourceRecordLimit (b.env degreeExponent)
    have df : Fr b d [sourceRecordLimit] := Fr.set _ _ (by simp)
    have dc : Cst d := Cst.of_fr br.constants df (by decide)
    have dframe : SourceFrame b d := SourceFrame.set b sourceRecordLimit _ (by decide)
    have de : d.env sourceRecordLimit=r.child.selected.1.e := br.exponent
    have he : r.child.selected.1.e<2^C.Wd := by
      rw [←br.exponent]
      exact br.valid.env_lt _
    refine Hs.then (emitCopies_run C .add d dc r.child.selected.1.e de he)
      (fun e ⟨eo,es,ec,efr⟩ n3 hn3=>?_)
    refine Hs.then (emitOperator_spec C .mul e ec)
      (fun f ⟨fo,fs,fc,ffr⟩ n4 hn4=>?_)
    refine Hs.last (emitOperator_spec C .sub f fc)
      (fun z ⟨zo,zs,zc,zfr⟩ n5 hn5=>?_)
    refine ⟨⟨?_,bf.trans (dframe.trans
      ((SourceFrame.of_rest es efr (by decide)).trans
        ((SourceFrame.of_rest fs ffr (by decide)).trans (SourceFrame.of_rest zs zfr (by decide))))),zc⟩,?_⟩
    · rw [zo,fo,eo]
      have dout : d.out=b.out := rfl
      rw [dout,bo]
    · have h0 : (tokWord (.const 0)).length=9 := by decide
      have ha : (tokWord .add).length=5 := by decide
      have hm : (tokWord .mul).length=7 := by decide
      have hs : (tokWord .sub).length=7 := by decide
      rw [h0] at hn1
      rw [ha] at hn3
      rw [hm] at hn4
      rw [hs] at hn5
      unfold amplifierTailCost
      omega
  obtain ⟨b,n,he,hn,bo,bf,bc⟩:=hh
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bo,h.of_frame bc hv bf,bf⟩

end NearQuarticWires.StageLiftTokens
