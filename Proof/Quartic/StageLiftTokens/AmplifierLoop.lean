import Proof.Quartic.StageLiftTokens.AmplifierTerm

/-!
# Every original BT summand

`imp:amp` and `lem:print`, paper/paper.tex: the actual exponent controls a counted loop which computes
each integer coefficient and replays the complete Fermat source once
for every original ordinal, including the zeroth power.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats StageLift

variable {B1 B2 : ℕ}

def amplifierLoop : St VV MM := forS amplifierIndex degreeExponent amplifierTerm

def amplifierLoopCost (E J e : ℕ) : ℕ := e*(amplifierTermCost E J+4)+4

theorem amplifierLoop_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C amplifierLoop a (amplifierLoopCost E r.child.selected.1.J r.child.selected.1.e) (fun b=>
      b.out=a.out++(List.ofFn fun j : Fin r.child.selected.1.e=>
        (toks (amplifierTermFormula r j.val)).flatMap tokWord).flatten ∧
      SourceReady C r b E ∧ SourceFrame a b) := by
  have he : r.child.selected.1.e<2^C.Wd := by
    apply source_count_capacity E C.Wd _ h.envelope_pos h.width
    have hb:=h.exponent_bound
    have hp:=Nat.le_self_pow (by decide : 3≠0) (E+1)
    omega
  refine (source_forFin C r a E amplifierIndex degreeExponent (by decide) (by decide) (by decide)
    amplifierTerm r.child.selected.1.e (amplifierTermCost E r.child.selected.1.J)
    (fun j=>(toks (amplifierTermFormula r j.val)).flatMap tokWord)
    he h h.exponent (fun _=>True) trivial (by intros; trivial) ?_).mono le_rfl ?_
  · intro j b hb _ bj _bm
    refine (amplifierTerm_run C r b E hb j bj).mono le_rfl ?_
    rintro d ⟨doo,dr,df,dj⟩
    exact ⟨doo,dr,df,trivial,dj,dr.exponent⟩
  · rintro b ⟨bo,br,bf,_,_,_⟩
    exact ⟨bo,br,bf⟩

end NearQuarticWires.StageLiftTokens
