import Proof.Quartic.StageCertNative.IndexedSourceRead
import Proof.Quartic.StageCert.MomentFramedMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

/-- `lem:print`, paper/paper.tex: a physical
prefix-index request is copied into the exact original suffix-index
source grammar before the already fixed complete source computation. -/
def indexedSourceBody : St VV MM := .seq readIndexedMoment emitMomentSourceCopy

noncomputable def indexedSourceSteps {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  indexedReadSteps r+9*(Program.prepWord B1 B2 r.call r.witness).length+
    6*(40*r.word.length+43)+9

theorem indexedSourceBody_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=indexedMomentWord r)
    (hwidth : r.word.length+4≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C indexedSourceBody a (indexedSourceSteps r) (fun z=>z.out=a.out++r.word) := by
  have hsource:=readIndexedMoment_run C r [] a hc (by simpa only [List.append_nil] using hin)
    (by omega) hempty
  unfold indexedSourceBody
  apply Hx.hs
  refine Hs.then hsource (fun b ⟨bd,_bi,bs,bc⟩ n1 hn1=>?_)
  have boutput : b.out=a.out := congrArg Prod.fst bs
  have hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^C.Wd :=
    lt_of_le_of_lt (r.prep_length_le.trans (by omega)) Nat.lt_two_pow_self
  refine Hs.last (emitMomentSourceCopy_run C r b bc bd r.word.length
    (fun value hv=>r.value_bits value hv) (by omega)
    (lt_of_le_of_lt (by omega) Nat.lt_two_pow_self) hfit)
    (fun z ⟨zo,_zs,_zc,_zf⟩ n2 hn2=>?_)
  exact ⟨by rw [zo,boutput],by dsimp only [indexedSourceSteps];omega⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the original prefix-index decoder and exact source
copy are initialized and framed by actual ordinary operations. -/
def indexedSourceProgram : St VV MM :=
  .seq initP (StageMain.framedOutputProgram indexedSourceBody)

theorem indexedSourceProgram_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (hin : C.inp=indexedMomentWord r) (hwidth : r.word.length+4≤C.Wd) :
    Hs C indexedSourceProgram (a0 : DS VV MM) (3*indexedSourceSteps r+8)
      (fun z=>z.out=frame r.word) := by
  unfold indexedSourceProgram
  refine (Hs.seq (t2:=3*indexedSourceSteps r+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=indexedSourceBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hwidth
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame r.word
  rw [ho,hout,List.nil_append]

end NearQuarticWires.StageCertNative
