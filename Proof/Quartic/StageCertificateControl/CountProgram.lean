import Proof.Quartic.StageCertificateControl.CountCore
import Proof.Quartic.StageLift.Literal
import Proof.Quartic.StageRecovery.OutputFrame
import Proof.Gates.Cells.Prelude

/-!
# A cold exact test-count header

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
the default in `sec:params`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- The scalar bootstrap of `sec:algorithm`, paper/paper.tex, inspects the real preparation tag before reading any
original-call fields; a default emits count zero. -/
def countUnframedProgram : St VV MM :=
  .seq initP (.seq (.op (.rdI t0)) (.ite (.eq t0 vZ)
    (StageLift.emitLiteral (natWord 0)) (.seq (.op .bkI) countCore)))

/-- The actual cold count header for `sec:algorithm`,
paper/paper.tex, is returned in its complete outer frame. -/
def countProgram : St VV MM := StageRecovery.OutputFrame.framedProgram countUnframedProgram

/-- The default branch of `sec:params`, paper/paper.tex, supplies a literal zero count without inspecting any following
bytes, and charges every scalar-codec output instruction. -/
theorem countUnframedProgram_default (C : Ctx) (rest : List Bool)
    (hin : C.inp=false::rest) (hroom : 2<2^C.Wd) :
    Hs C countUnframedProgram (a0 : DS VV MM) 16 (fun b => b.out=natWord 0) := by
  unfold countUnframedProgram
  refine Hs.seq (t2 := 10)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl hroom)
    fun a ⟨hac,_,_,hai,hao,_,_,_,_⟩ => ?_
  change a.ip=0 at hai
  change a.out=[] at hao
  refine Hs.seq (t2 := 8) (hs_rdI C t0 a (by rw [hai,hin];exact Nat.succ_pos _)) fun b hb => ?_
  subst b
  let afterTag := {a.set t0 (bitOf C.inp a.ip) with ip := a.ip+1}
  have hat : Cst afterTag := Cst.of_fr (T := [t0]) hac (Fr.set _ _ (by decide)) (by decide)
  have ht : (Cnd.eq t0 vZ).eval afterTag=true := by
    simp (config := {decide := true}) [Cnd.eval,afterTag,DS.set,bitOf,hai,hin,hac.z]
  refine Hs.iteT (c := .eq t0 vZ) (show t0≠vZ by decide) ht ?_
  refine (StageLift.emitLiteral_spec C (natWord 0) afterTag hat).mono (by decide) ?_
  rintro b ⟨hbo,_,_,_⟩
  simpa only [afterTag,DS.set_out,hao,List.nil_append] using hbo

/-- The selected scalar bootstrap of `sec:algorithm` and
`prop:time`, paper/paper.tex,
starts from the actual empty state and prints the complete test
census from original raw-call bits and selected public parameters. -/
theorem countUnframedProgram_selected (C : Ctx) (c : Call) (p : Cells.Parameters) (rest : List Bool)
    (hin : C.inp=true::(callWord c++Program.parametersWord p++rest))
    (hcall : (callWord c).length+2≤C.Wd)
    (hwidth : 64*(StageCertTests.scheduleHint p+1)≤C.Wd) :
    Hs C countUnframedProgram (a0 : DS VV MM)
      (countCoreCost c p (StageCertTests.scheduleHint p)+11)
      (fun b => b.out=natWord (StageCertTests.certificateMetadata p c.kind).length) := by
  let cost := countCoreCost c p (StageCertTests.scheduleHint p)
  have bounds := StageCertTests.scheduleBounds_of_width C p hwidth
  have hroom : 2<2^C.Wd := by have := bounds.small;omega
  unfold countUnframedProgram
  refine (Hs.seq (t2 := cost+5)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl hroom)
    fun a ⟨hac,harm,harc,hai,hao,_,_,_,_⟩ => ?_).mono (by omega) (fun _ h => h)
  change a.ip=0 at hai
  change a.out=[] at hao
  refine (Hs.seq (t2 := cost+3)
    (hs_rdI C t0 a (by rw [hai,hin];exact Nat.succ_pos _)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let afterTag := {a.set t0 (bitOf C.inp a.ip) with ip := a.ip+1}
  have hat : Cst afterTag := Cst.of_fr (T := [t0]) hac (Fr.set _ _ (by decide)) (by decide)
  have ht : (Cnd.eq t0 vZ).eval afterTag=false := by
    simp (config := {decide := true}) [Cnd.eval,afterTag,DS.set,bitOf,hai,hin,hac.z]
  refine Hs.iteF (c := .eq t0 vZ) (show t0≠vZ by decide) ht ?_
  refine (Hs.seq (t2 := cost)
    (Hs.op (OpEx.bkI afterTag (by dsimp [afterTag];omega)) rfl) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := {afterTag with ip := afterTag.ip-1}
  have hstart : Cst start := ⟨hat.z,hat.one,hat.two⟩
  have hstarti : start.ip=0 := by dsimp [start,afterTag];omega
  have hstartout : start.out=[] := hao
  refine (countCore_spec C c p rest start hstart
    (by rw [hstarti,List.drop_zero];exact hin) hcall hwidth
    (by intro store;change a.ram store=[] ∧ a.rc store=0;rw [harm,harc];exact ⟨rfl,rfl⟩)).mono le_rfl ?_
  intro b hbo
  simpa only [hstartout,List.nil_append] using hbo

/-- The actual default count packet of `sec:params` and
`sec:algorithm`, paper/paper.tex, has the
complete frame and a fixed fully paid cold source clock. -/
theorem countProgram_default (C : Ctx) (rest : List Bool)
    (hin : C.inp=false::rest) (hroom : 2<2^C.Wd) :
    Hs C countProgram (a0 : DS VV MM) 50 (fun b => b.out=frame (natWord 0)) := by
  obtain ⟨b,n,eb,hn,hbo⟩ := countUnframedProgram_default C rest hin hroom
  have ef := StageRecovery.OutputFrame.framedProgram_spec eb
  refine ⟨StageRecovery.OutputFrame.framedState b,3*n+2,ef,by omega,?_⟩
  change frame b.out=_
  rw [hbo]

/-- The actual selected count packet of `sec:algorithm` and
`prop:time`, paper/paper.tex,
returns exactly the complete scalar frame from the original source. -/
theorem countProgram_selected (C : Ctx) (c : Call) (p : Cells.Parameters) (rest : List Bool)
    (hin : C.inp=true::(callWord c++Program.parametersWord p++rest))
    (hcall : (callWord c).length+2≤C.Wd)
    (hwidth : 64*(StageCertTests.scheduleHint p+1)≤C.Wd) :
    Hs C countProgram (a0 : DS VV MM)
      (3*(countCoreCost c p (StageCertTests.scheduleHint p)+11)+2)
      (fun b => b.out=frame (natWord (StageCertTests.certificateMetadata p c.kind).length)) := by
  obtain ⟨b,n,eb,hn,hbo⟩ := countUnframedProgram_selected C c p rest hin hcall hwidth
  have ef := StageRecovery.OutputFrame.framedProgram_spec eb
  refine ⟨StageRecovery.OutputFrame.framedState b,3*n+2,ef,by omega,?_⟩
  change frame b.out=_
  rw [hbo]

end NearQuarticWires.StageCertificateControl
