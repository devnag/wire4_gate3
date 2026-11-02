import Proof.Quartic.StagePrint.ContextTarget
import Proof.Quartic.StagePrint.CompactHeader
import Proof.Quartic.StageMain.CompactInitialize
import Proof.Quartic.StageMain.CompactBounds
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests StageMain.Compact

/-- `lem:print`, paper/paper.tex: initialize
and retain the actual successful preparation's original finite source. -/
def acquireContext : St VV MM := .seq initP initializeCompact

/-- `prop:time`, paper/paper.tex: the source
clock pays all actual original-call, parameter and witness reads. -/
noncomputable def readSteps {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  6+initializeCost r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness) r.word.length

/-- `lem:print` and `prop:time`, paper/paper.tex: the sole initial input is the literal preparation;
actual parsing establishes the retained call, public fields and witness. -/
theorem acquireContext_run {B1 B2 : ℕ} (C : Ctx) (r : PreparedScheduleRequest B1 B2)
    (hin : C.inp=r.word) (hW : r.word.length+2≤C.Wd) :
    Hs C acquireContext (a0 : DS VV MM) (readSteps r) (fun b=>
      Decoded r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness) b ∧
      b.out=[] ∧ Cst b ∧ Valid C b) := by
  have hword : r.word=compactInput r.call r.selected.1
      (Program.witnessPrefix r.call r.selected.1 r.witness) :=
    prepWord_eq_compact r.dispatched r.witness
  have bounds:=compact_decoder_bounds r.call r.selected.1
    (Program.witnessPrefix r.call r.selected.1 r.witness) C.Wd (by rwa [←hword])
  have hpow : 2<2^C.Wd := by
    have hh:=Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) (by omega : 2≤C.Wd)
    norm_num at hh
    omega
  have hrun : Hs C acquireContext (a0 : DS VV MM) (readSteps r) (fun b=>
      Decoded r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness) b ∧
      b.out=[] ∧ Cst b) := by
    unfold acquireContext
    refine (Hs.seq (t2:=initializeCost r.call r.selected.1
      (Program.witnessPrefix r.call r.selected.1 r.witness) r.word.length)
      (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl hpow) ?_).mono
      (by unfold readSteps;omega) (fun _ h=>h)
    rintro a ⟨hc,hram,hrc,hip,hout,_hkin,_hkout,_hkc,_hfr⟩
    have he:=initialize_run C r.call r.selected.1 r.word.length
      (Program.witnessPrefix r.call r.selected.1 r.witness) [] a hc
      (by rw [hip,hin];simpa only [a0,List.drop_zero,List.append_nil] using hword)
      bounds.1 bounds.2.1
      (by simpa only [←hword] using bounds.2.2.1) hW bounds.2.2.2
      (by intro store _hstore;rw [hram,hrc];exact ⟨rfl,rfl⟩)
    refine he.mono le_rfl ?_
    rintro b ⟨_hbip,hdecoded,_hlen,_hcompact,_hcursor,hrest,hbc,_hframe⟩
    refine ⟨hdecoded,?_,hbc⟩
    have hbo:=congrArg Prod.fst hrest
    exact hbo.trans hout
  refine (StagePrint.source_addValid (by omega) (a0_valid C) hrun).mono le_rfl ?_
  rintro b ⟨⟨hd,ho,hc⟩,hv⟩
  exact ⟨hd,ho,hc,hv⟩

end NearQuarticWires.StagePrintContext
