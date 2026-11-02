import Proof.Quartic.StageResize.Cost
import Proof.Quartic.StageRecovery.NaturalPrint
import Proof.Quartic.StageRecovery.OutputFrame
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the only width
input is the actual original stacking-width codec; L is computed by a
real increment before serialization, rather than supplied to setup. -/
def widthRegister : Fin VV := 20

def widthBody : St VV MM :=
  .seq (StageGamma.readField widthRegister)
    (.seq (.op (.inc widthRegister)) (StageRecovery.emitVariable widthRegister))

def widthBodyClock (W : ℕ) : ℕ := 30*natBitLength W+40*natBitLength (W+1)+100

theorem widthBody_spec (C : Ctx) (W : ℕ) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=natWord W)
    (hwidth : W+natBitLength W+10≤C.Wd) :
    Hs C widthBody a (widthBodyClock W) (fun d=>d.out=a.out++natWord (W+1)) := by
  have hcap : W+4<2^C.Wd := by have hh:=Nat.lt_two_pow_self (n:=C.Wd);omega
  unfold widthBody
  refine Hx.hs (Hs.then (StageGamma.readField_spec C widthRegister (by decide) (by decide)
    a hc W [] (by simpa only [List.append_nil] using hin) (by omega)) ?_)
  rintro b ⟨bw,_,brest,bc,_⟩ k0 hk0
  have bout : b.out=a.out := congrArg Prod.fst brest
  refine Hs.then (hs_inc C widthRegister b (by rw [bw];omega)) ?_
  rintro c rfl k1 hk1
  have cc : Cst (b.set widthRegister (b.env widthRegister+1)) :=
    bc.of_fr (Fr.set b _ (by simp : widthRegister∈[widthRegister])) (by decide)
  have cw : (b.set widthRegister (b.env widthRegister+1)).env widthRegister=W+1 := by
    rw [DS.set_env_self,bw]
  refine Hs.last (StageRecovery.emitVariable_spec C _ cc widthRegister (by decide)
    (by omega) (by rw [cw];have hh:=StageResize.bitLength_le (W+1);omega)) ?_
  rintro d ⟨dout,_,_,_⟩ k2 hk2
  refine ⟨?_,?_⟩
  · rw [dout,cw]
    change b.out++natWord (W+1)=_
    rw [bout]
  · rw [cw] at hk2
    unfold widthBodyClock
    omega

def widthRawProgram : St VV MM := .seq initP widthBody

def widthRawClock (W : ℕ) : ℕ := widthBodyClock W+6

theorem widthRawProgram_spec (C : Ctx) (W : ℕ) (hin : C.inp=natWord W)
    (hwidth : W+natBitLength W+10≤C.Wd) :
    Hs C widthRawProgram (a0 : DS VV MM) (widthRawClock W) (fun d=>d.out=natWord (W+1)) := by
  have htwo : 2<2^C.Wd := by
    have hh:=Nat.lt_two_pow_self (n:=C.Wd)
    omega
  unfold widthRawProgram widthRawClock
  refine (Hs.seq (t1:=5) (t2:=widthBodyClock W)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl htwo) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,_,_,hi,ho,_,_,_,_⟩
  refine (widthBody_spec C W a hc (by rw [hi];change C.inp.drop 0=natWord W;rw [List.drop_zero,hin])
    hwidth).mono le_rfl ?_
  rintro d hd
  simpa only [ho,a0,List.nil_append] using hd

def widthProgram : St VV MM := StageRecovery.OutputFrame.framedProgram widthRawProgram

def widthSourceClock (W : ℕ) : ℕ := 3*widthRawClock W+2

theorem widthProgram_spec (C : Ctx) (W : ℕ) (hin : C.inp=natWord W)
    (hwidth : W+natBitLength W+10≤C.Wd) :
    Hs C widthProgram (a0 : DS VV MM) (widthSourceClock W) (fun d=>d.out=frame (natWord (W+1))) := by
  obtain ⟨b,k,he,hk,ho⟩:=widthRawProgram_spec C W hin hwidth
  have hh:=StageRecovery.OutputFrame.framedProgram_spec he
  exact ⟨StageRecovery.OutputFrame.framedState b,3*k+2,hh,
    by unfold widthSourceClock;omega,by change frame b.out=_;rw [ho]⟩

def widthSizes : Sz := ⟨100,1,0,0,0,0⟩

theorem widthContext (W : ℕ) :
    W+natBitLength W+10≤widthSizes.W (leadOnes (natWord W)) := by
  have hv:=lt_natBitLength W
  have hl:=Nat.lt_two_pow_self (n:=natBitLength W)
  have hp:=Nat.one_le_two_pow (n:=natBitLength W)
  simp only [widthSizes,Sz.W,one_mul]
  have hlead : leadOnes (natWord W)=natBitLength W := by
    simpa only [List.append_nil] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord W []
  rw [hlead]
  omega

/-- `prop:time`, paper/paper.tex: width arithmetic
uses only its small actual width packet and its own ordinary setup. -/
noncomputable def widthBudget (W : ℕ) : ℕ :=
  langBudget StageResize.resizeCallee widthSizes VV MM (natWord W) (widthSourceClock W)

noncomputable def widthWordFunction :
    WordFunction ℕ natWord (fun W=>frame (natWord (W+1))) widthBudget :=
  wordFunction_of_lang natWord (fun W=>frame (natWord (W+1))) StageResize.resizeCallee
    widthSizes widthProgram widthSourceClock (by
      intro W
      obtain ⟨b,k,he,hk,ho⟩:=widthProgram_spec
        (ctxOf StageResize.resizeCallee widthSizes (natWord W)) W rfl (widthContext W)
      exact ⟨b,k,he,ho,hk⟩) (by
      intro W
      have hh:=widthContext W
      omega)

end NearQuarticWires.StageTupleSetup
