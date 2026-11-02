import Proof.Quartic.StageLiftTokens.Rows

/-!
# The two original circuit passes

`lem:residue` and `lem:print`, paper/paper.tex: each circuit contributes its score factor followed by
all J digit factors, including absent-circuit zeros. The physical
outer loop retains the amplifier ordinal and the complete source.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

noncomputable def circuitFactorWord (r : Greedy.PrintRequest B1 B2) (j : Fin 2) : List Bool :=
  (toks (requestFactor r (j,none))).flatMap tokWord++
    (List.ofFn fun row : Fin (r.child.selected.1.J-1+1)=>
      (toks (requestFactor r (j,some row))).flatMap tokWord).flatten

def circuitProgram : St VV MM := .seq scoreFactor rowsProgram

def circuitSourceCost (E J : ℕ) : ℕ := factorSourceCost E+rowSourceCost E J+1

theorem circuitProgram_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env targetCircuit=j.val) :
    Hs C circuitProgram a (circuitSourceCost E r.child.selected.1.J) (fun b=>
      b.out=a.out++circuitFactorWord r j ∧ SourceReady C r b E ∧ SourceFrame a b ∧
      b.env targetCircuit=j.val ∧ b.env amplifierIndex=a.env amplifierIndex) := by
  unfold circuitProgram circuitSourceCost
  refine Hs.seq (scoreFactor_run C r a E h j hj) ?_
  rintro b ⟨bo,br,bf,bfr⟩
  refine (rowsProgram_run C r b E br j ((bfr _ (by decide)).trans hj)).mono le_rfl ?_
  rintro d ⟨doo,dr,df,dj,di⟩
  exact ⟨by simpa only [circuitFactorWord,List.append_assoc] using doo.trans (congrArg (fun l=>l++_) bo),
    dr,bf.trans df,dj,di.trans (bfr _ (by decide))⟩

noncomputable def allFactorWord (r : Greedy.PrintRequest B1 B2) : List Bool :=
  (List.ofFn (circuitFactorWord r)).flatten

def allFactorsProgram : St VV MM := forS targetCircuit v2 circuitProgram

def allFactorCost (E J : ℕ) : ℕ := 2*(circuitSourceCost E J+4)+4

theorem allFactorsProgram_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) :
    Hs C allFactorsProgram a (allFactorCost E r.child.selected.1.J) (fun b=>
      b.out=a.out++allFactorWord r ∧ SourceReady C r b E ∧ SourceFrame a b ∧
      b.env amplifierIndex=a.env amplifierIndex) := by
  have h2 : 2<2^C.Wd := by
    have hw:=Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) h.width_five
    norm_num at hw
    omega
  have hh:=source_forFin C r a E targetCircuit v2 (by decide) (by decide) (by decide)
    circuitProgram 2 (circuitSourceCost E r.child.selected.1.J) (circuitFactorWord r)
    h2 h h.constants.two (fun _=>True) trivial (by intros; trivial) (by
      intro j b hb _ bj _bm
      refine (circuitProgram_run C r b E hb j bj).mono le_rfl ?_
      rintro d ⟨doo,dr,df,dj,_di⟩
      exact ⟨doo,dr,df,trivial,dj,dr.constants.two⟩)
  obtain ⟨b,n,he,hn,bo,br,bf,_bR,_bi,_bm⟩:=hh
  exact ⟨b,n,he,hn,bo,br,bf,avoidsRegister_spec he (by decide)⟩

end NearQuarticWires.StageLiftTokens
