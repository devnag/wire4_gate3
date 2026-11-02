import Proof.Quartic.StageLiftTokens.TokenRun

/-!
# Active and absent circuit tokens

`lem:residue` and Step 3, paper/paper.tex: circuit zero is always present; circuit one is present
exactly for the actual two-circuit kind. An absent circuit contributes
a literal zero form and zero target to every original Fermat factor.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageLift

variable {B1 B2 : ℕ}

def zeroPair : St VV MM := .seq (emitOperator (.const 0)) (emitOperator (.const 0))

def activePair (yes : St VV MM) : St VV MM :=
  .ite (.eq targetCircuit vZ) yes (.ite (.eq callKindVar v1) yes zeroPair)

theorem zeroPair_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C zeroPair a 39 (fun b=>
      b.out=a.out++tokWord (.const 0)++tokWord (.const 0) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b [vJ]) := by
  unfold zeroPair
  have hlen : 2*(tokWord (.const 0)).length+1=19 := by decide
  have hs:=emitOperator_ready C r a E h (.const 0)
  rw [hlen] at hs
  refine Hs.seq (t2 := 19) hs ?_
  rintro b ⟨bo,br,bf,bfr⟩
  have hs:=emitOperator_ready C r b E br (.const 0)
  rw [hlen] at hs
  refine hs.mono le_rfl ?_
  rintro d ⟨doo,dr,df,dfr⟩
  exact ⟨by rw [doo,bo],dr,bf.trans df,bfr.trans dfr⟩

theorem activePair_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env targetCircuit=j.val)
    (yes : St VV MM) (t : ℕ) (word : List Bool) (T : List (Fin VV)) (ht : 39≤t)
    (hy : Hs C yes a t (fun b=>b.out=a.out++word ∧ SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b T)) :
    Hs C (activePair yes) a (t+2) (fun b=>
      b.out=a.out++(if j∈Builder.circuitSet r.child.call then word
        else tokWord (.const 0)++tokWord (.const 0)) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (T++[vJ])) := by
  let R : DS VV MM→Prop := fun b=>
    b.out=a.out++(if j∈Builder.circuitSet r.child.call then word
      else tokWord (.const 0)++tokWord (.const 0)) ∧
    SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (T++[vJ])
  have keep (hjmem : j∈Builder.circuitSet r.child.call) : Hs C yes a t R := by
    refine hy.mono le_rfl ?_
    rintro b ⟨bo,br,bf,bfr⟩
    exact ⟨by simpa only [if_pos hjmem] using bo,br,bf,
      bfr.weaken (by intro x hx; exact List.mem_append_left _ hx)⟩
  have blank (hjmem : j∉Builder.circuitSet r.child.call) : Hs C zeroPair a t R := by
    refine (zeroPair_run C r a E h).mono ht ?_
    rintro b ⟨bo,br,bf,bfr⟩
    exact ⟨by simpa only [if_neg hjmem,List.append_assoc] using bo,br,bf,
      bfr.weaken (by intro x hx; exact List.mem_append_right _ hx)⟩
  unfold activePair
  refine Hs.ite (t := t+1) (c := .eq targetCircuit vZ) (show targetCircuit≠vZ by decide) ?_ ?_
  · intro he
    have hj0 : j.val=0 := by simpa only [Cnd.eval,hj,h.constants.z,decide_eq_true_eq] using he
    exact (keep ((activeCircuit_from_kind r.child.call j).mpr (Or.inl hj0))).mono (by omega) (fun _ hb=>hb)
  · intro he
    have hj0 : j.val≠0 := by simpa only [Cnd.eval,hj,h.constants.z,decide_eq_false_iff_not] using he
    refine Hs.ite (t := t) (c := .eq callKindVar v1) (show callKindVar≠v1 by decide) ?_ ?_
    · intro hk
      have hk1 : kindTag r.child.call.kind=1 := by
        simpa only [Cnd.eval,h.kind,h.constants.one,decide_eq_true_eq] using hk
      exact keep ((activeCircuit_from_kind r.child.call j).mpr (Or.inr hk1))
    · intro hk
      have hk1 : kindTag r.child.call.kind≠1 := by
        simpa only [Cnd.eval,h.kind,h.constants.one,decide_eq_false_iff_not] using hk
      exact blank (fun hm=>((activeCircuit_from_kind r.child.call j).mp hm).elim hj0 hk1)

end NearQuarticWires.StageLiftTokens
