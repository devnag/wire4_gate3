import Proof.Quartic.StageFormulaMetadata.FiniteInitialize

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms

variable {V M : ℕ}

/-- `prop:time`, paper/paper.tex: the formatter
uses binary registers sized by its actual measured finite source. -/
def finiteContext (K : Callee) (bits : List Bool) : Ctx :=
  ⟨finiteWidth bits.length,bits,K,0,0⟩

/-- `prop:time`, paper/paper.tex: the complete
program measures its input before cell setup, execution and teardown. -/
noncomputable def finiteProgram (K : Callee) (main : St V M) :
    WMX (NS M (TSK K) V) (NR M) :=
  .seq (finiteInitialize K) (.seq (comp K main) tearP)

/-- `prop:time`, paper/paper.tex: the ledger
includes every measured setup, compiled binary operation, finite
store rewind and final return of the input and output heads. -/
def finiteBudget (K : Callee) (variableCount stores : ℕ) (bits : List Bool)
    (steps : ℕ) : ℕ :=
  let width:=finiteWidth bits.length
  finiteInitializeCost variableCount stores bits.length+1+
    (steps*(500*(width+1)^2+100*(TSK K+3))+1+
      (10*bits.length+5*steps+15+stores*(5*((2*width+1)*steps)+2)+10))

/-- `prop:time`, paper/paper.tex: the actual
finite-source setup and compiled language semantics yield one fixed
ordinary multitape word function with an explicit complete clock. -/
noncomputable def wordFunction_of_finite {Request : Type}
    (input output : Request→List Bool) (K : Callee) (main : St V M)
    (steps : Request→ℕ)
    (hrun : ∀ request, ∃ b n,
      Ex (finiteContext K (input request)) main a0 b n ∧
      b.out = output request ∧ n ≤ steps request) :
    WordFunction Request input output
      (fun request=>finiteBudget K V M (input request) (steps request)) :=
  NearCubicGates.Close.Interfaces.wordFunction_of_wmx (finiteProgram K main) sOUT
    (by simp) (fun request=>2*(input request).length+8*finiteWidth (input request).length+40+
      (2*finiteWidth (input request).length+1)*(steps request+1)*(M+1)+steps request) (by
    intro request
    obtain ⟨b,n,hex,hout,hn⟩:=hrun request
    let C:=finiteContext K (input request)
    let width:=finiteWidth (input request).length
    let cap:=2*(input request).length+8*width+40+
      (2*width+1)*(steps request+1)*(M+1)+steps request
    have hwidth : 1≤C.Wd := by dsimp [C,finiteContext,finiteWidth];omega
    have hreserve : 2*width+1≤(2*width+1)*(steps request+1)*(M+1) := by
      rw [Nat.mul_assoc]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    have hsetup:=finiteInitialize_spec (V:=V) (M:=M) K (input request) cap
      (by dsimp [cap];omega)
    have henc : Enc C (a0 : DS V M) (initSt (t:=TS C) C.Wd C.Lk C.Bk C.inp) :=
      initSt_enc C
    have hcapok : CapOK C cap (a0 : DS V M) n := by
      refine ⟨hwidth,?_,?_,?_,fun _=>?_,?_⟩
      · change 2*width+2≤cap
        dsimp [cap];omega
      · change 2*(input request).length+2≤cap
        dsimp [cap];omega
      · change 0+n≤cap
        dsimp [cap];omega
      · change (2*width+1)*(0+n+1)+1≤cap
        simp only [Nat.zero_add]
        have hprod : (2*width+1)*(n+1)≤(2*width+1)*(steps request+1)*(M+1) := by
          calc (2*width+1)*(n+1)≤(2*width+1)*(steps request+1) :=
              Nat.mul_le_mul_left _ (by omega)
            _≤_ := Nat.le_mul_of_pos_right _ (by omega)
        dsimp [cap];omega
      · change 2*0+0+3+2≤cap
        dsimp [cap];omega
    obtain ⟨⟨state,hstate,exec⟩,_⟩:=comp_ok C cap (callee_hB C) hex
      (a0_valid C) _ henc hcapok
    have hvalid:=hex.valid hwidth (callee_hB C) (a0_valid C)
    have houtlen:=hex.out_len
    have hramlen:=hex.ram_len
    have hcursor : ∀ store,b.rc store≤n := fun store=>by
      have h1:=hvalid.rc_le store
      have h2:=hramlen store
      simp only [a0,List.length_nil,Nat.zero_add] at h2
      omega
    have hsum:=sum_rc_le n hcursor
    have hmem : (2*C.Wd+1)*∑ store:Fin M,b.rc store≤
        (2*width+1)*(steps request+1)*(M+1) := by
      calc (2*C.Wd+1)*∑ store:Fin M,b.rc store≤(2*width+1)*(M*n) :=
          Nat.mul_le_mul_left _ hsum
        _≤(2*width+1)*((steps request+1)*(M+1)) :=
          Nat.mul_le_mul_left _ (by nlinarith)
        _=_ := by ring
    have hinput:=hvalid.ip_le
    have hkin:=hvalid.kin_le
    have hkout:=hvalid.kout_le
    have hkc:=hvalid.kc_le
    change b.kin.length ≤ 0 at hkin
    change b.kout.length ≤ 3 at hkout
    simp only [a0,List.length_nil,Nat.zero_add] at houtlen
    have hkin0 : b.kin.length=0 := Nat.eq_zero_of_le_zero hkin
    have hko : b.kout.length≤3 := hkout
    obtain ⟨final,htear,hfinalout,hfinalstreams,hfinalregs⟩:=tear_spec C b state hstate cap (by
      change 2*b.ip+b.out.length+2*b.kin.length+b.kc+
        (2*C.Wd+1)*∑ store:Fin M,b.rc store≤cap
      change b.ip≤(input request).length at hinput
      dsimp [cap]
      omega)
    refine ⟨final,(WXExec.seq hsetup (WXExec.seq exec htear)).mono ?_,
      hfinalout.trans hout,hfinalstreams,hfinalregs⟩
    have hclock : tearCost C b≤10*(input request).length+5*steps request+15+
        M*(5*((2*width+1)*steps request)+2)+10 := by
      have hstores : ((List.finRange M).map fun store=>5*((2*C.Wd+1)*b.rc store)+2).sum≤
          M*(5*((2*width+1)*steps request)+2) := by
        have hbound:=List.sum_le_card_nsmul
          ((List.finRange M).map fun store=>5*((2*C.Wd+1)*b.rc store)+2)
          (5*((2*width+1)*steps request)+2) (by
            intro value hv
            obtain ⟨store,_,rfl⟩:=List.mem_map.mp hv
            change 5*((2*width+1)*b.rc store)+2≤5*((2*width+1)*steps request)+2
            have hmul:=Nat.mul_le_mul_left (2*width+1) ((hcursor store).trans hn)
            omega)
        simpa using hbound
      unfold tearCost
      change b.ip≤(input request).length at hinput
      omega
    have hcompiled:=Nat.mul_le_mul_right (500*(width+1)^2+100*(TSK K+3)) hn
    unfold finiteBudget
    change _≤finiteInitializeCost V M (input request).length+1+
      (steps request*(500*(width+1)^2+100*(TSK K+3))+1+_)
    change _≤_ at hcompiled
    dsimp only [KC,TS,C,finiteContext] at *
    dsimp only [width] at *
    omega)

end NearQuarticWires.StageFormulaMetadata
