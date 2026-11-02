import Proof.Quartic.StageCertificateControl.PreparedFold
import Proof.Gates.Cells.Prelude
import Proof.Quartic.StageRecovery.OutputFrame

/-!
# The cold complete certificate bitmap program

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
the default branch of `sec:params`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- Step 2 of `sec:algorithm` and the default of `sec:params`,
paper/paper.tex: initialize the real
empty machine, inspect the literal preparation tag, and either emit
an empty suffix or run the complete original-source bitmap computation. -/
def bitmapProgram : St VV MM :=
  .seq initP (.seq (.op (.rdI t0))
    (.ite (.eq t0 vZ) (.op (.emit false)) (.seq (.op .bkI) (StageRecovery.OutputFrame.framedProgram preparedFold))))

/-- The default of `sec:params` and Step 2, paper/paper.tex: every false preparation tag emits exactly the
empty framed suffix without scanning its following bytes. -/
theorem bitmapProgram_default (C : Ctx) (rest : List Bool)
    (hin : C.inp=false::rest) (hroom : 2<2^C.Wd) :
    Hs C bitmapProgram (a0 : DS VV MM) 10 (fun b => b.out=frame []) := by
  unfold bitmapProgram
  refine Hs.seq (t2 := 4)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl hroom)
    fun a ⟨hac,_,_,hai,hao,_,_,_,_⟩ => ?_
  change a.ip=0 at hai
  change a.out=[] at hao
  refine Hs.seq (t2 := 2) (hs_rdI C t0 a (by rw [hai,hin];exact Nat.succ_pos _)) fun b hb => ?_
  subst b
  have ht : (Cnd.eq t0 vZ).eval {a.set t0 (bitOf C.inp a.ip) with ip := a.ip+1}=true := by
    simp (config := {decide := true}) [Cnd.eval,DS.set,bitOf,hai,hin,hac.z]
  refine (Hs.iteT (c := .eq t0 vZ) (show t0≠vZ by decide) ht (hs_emit C false _)).mono le_rfl ?_
  rintro b rfl
  change a.out++[false]=frame []
  rw [hao]
  rfl

/-- The cold whole-bitmap computation in `sec:algorithm` and
`prop:time`, paper/paper.tex,
starts with empty stores, parses the actual preparation and count
header, tests all signed columns, and emits exactly the final prefix. -/
theorem bitmapProgram_selected (C : Ctx) (c : Call) (p : Cells.Parameters) (B : ℕ)
    (witness : List Bool) (tests : List NativeTest) (rest : List Bool)
    (hin : C.inp=true::(callWord c++Program.parametersWord p++frame witness++
      natWord tests.length++nativeTestStream tests++rest))
    (hcall : (callWord c).length+2≤C.Wd)
    (hfields : ∀ value∈StageLift.parameterHeadFields p++p.primes.sort (·≤·)++
      StageLift.parameterTailFields p++p.factors,natBitLength value≤B)
    (hB : B+2≤C.Wd) (hcounts : p.primes.card<2^C.Wd ∧ p.factors.length<2^C.Wd)
    (hkn : p.k≤c.n) (hnwidth : c.n+2≤C.Wd)
    (htests : ∀ test∈tests,test.values.length=paddedCount c.n p.k)
    (hTword : natBitLength tests.length+2≤C.Wd) (hTfit : tests.length<2^C.Wd)
    (hvalues : ∀ test∈tests,∀ z∈test.values,encS z<2^test.width)
    (hwidth : ∀ test∈tests,test.width+2≤C.Wd)
    (hboundWord : ∀ test∈tests,natBitLength test.bound+2≤C.Wd)
    (hwidthWord : ∀ test∈tests,natBitLength test.width+2≤C.Wd) :
    Hs C bitmapProgram (a0 : DS VV MM) (3*preparedFoldCost c p B witness tests+13) (fun b =>
      b.out=frame (frame ((nativeTestFlags tests (List.replicate (paddedCount c.n p.k) true)).take
        (centerCount c.n p.k)))) := by
  have hroom : 2<2^C.Wd := by
    have hh := Nat.lt_two_pow_self (n := C.Wd)
    omega
  let cost := preparedFoldCost c p B witness tests
  unfold bitmapProgram
  refine (Hs.seq (t2 := 3*cost+7)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl hroom)
    fun a ⟨hac,harm,harc,hai,hao,_,_,_,_⟩ => ?_).mono (by omega) (fun _ h => h)
  change a.ip=0 at hai
  change a.out=[] at hao
  refine (Hs.seq (t2 := 3*cost+5)
    (hs_rdI C t0 a (by rw [hai,hin];exact Nat.succ_pos _)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let afterTag := {a.set t0 (bitOf C.inp a.ip) with ip := a.ip+1}
  have hat : Cst afterTag := Cst.of_fr (T := [t0]) hac (Fr.set _ _ (by decide)) (by decide)
  have ht : (Cnd.eq t0 vZ).eval afterTag=false := by
    simp (config := {decide := true}) [Cnd.eval,afterTag,DS.set,bitOf,hai,hin,hac.z]
  refine Hs.iteF (c := .eq t0 vZ) (show t0≠vZ by decide) ht ?_
  refine (Hs.seq (t2 := 3*cost+2)
    (Hs.op (OpEx.bkI afterTag (by dsimp [afterTag];omega)) rfl) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := {afterTag with ip := afterTag.ip-1}
  have hstart : Cst start := ⟨hat.z,hat.one,hat.two⟩
  have hstarti : start.ip=0 := by dsimp [start,afterTag];omega
  have hstartout : start.out=[] := hao
  obtain ⟨b,nb,eb,hnb,hbo⟩ := preparedFold_spec C c p B witness tests rest start hstart
    (by rw [hstarti,List.drop_zero];exact hin) hcall hfields hB hcounts
    (by intro store;change a.ram store=[] ∧ a.rc store=0;rw [harm,harc];exact ⟨rfl,rfl⟩)
    hkn hnwidth htests hTword hTfit hvalues hwidth hboundWord hwidthWord
  have hmark : StageRecovery.OutputFrame.markedState start=start := by
    unfold StageRecovery.OutputFrame.markedState
    have hm : StageRecovery.OutputFrame.markedBits start.out=start.out := by
      rw [hstartout]
      rfl
    rw [hm]
  have ef := StageRecovery.OutputFrame.framedProgram_spec eb
  rw [hmark] at ef
  refine ⟨StageRecovery.OutputFrame.framedState b,3*nb+2,ef,by omega,?_⟩
  change frame b.out=_
  rw [hbo,hstartout,List.nil_append]

end NearQuarticWires.StageCertificateControl
