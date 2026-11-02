import Proof.Quartic.StageLift.CarrierStartup
import Proof.Quartic.StageLift.SourceCalleeSizes
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `prop:time`, paper/paper.tex: one fixed source context allocates arithmetic and the
actual shared StructuralCold callee from the literal leading header. -/
noncomputable def printSourceContext (B1 B2 : ℕ) (input : List Bool) : Ctx :=
  ctxOf (StageCert.Tokens.structuralSourceCallee B1 B2) (printSourceSizes B1 B2) input

/-- Step 3 and `lem:print`, paper/paper.tex: initialize actual constants before the literal original
source, metadata and one-copy carrier prefix are generated. -/
def coldCarrierInitialize : St VV MM := .seq initP initializeCarrierSource

/-- Step 3 and `prop:time`, paper/paper.tex: the actual cold machine supplies the original source
and carrier prefix without any register, decoded-input, width, count,
Formula, source-provider or callee-budget premise. -/
theorem coldCarrierInitialize_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    Hs C coldCarrierInitialize (a0 : DS VV MM) (carrierStartupCost r + 6) (fun z =>
      z.out = natWord (preparedWordOf r).length ++ preparedWordOf r ++
        natWord (r.child.cellCall.seed.N ^ 8) ∧
      CarrierStartData r z ∧ C.inp.drop z.ip = [] ∧ z.kin = [] ∧ Cst z ∧ Valid C z) := by
  dsimp only
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  have hwidth : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd := by
    change 100 * (sourceEnvelope r + 1) ^ 2 ≤
      (printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r))
    simpa only [List.append_nil] using printSourceSizes_width r []
  have hsmall : 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.pow_pos (by omega)
  have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hi := StagePrint.source_addValid (by omega : 1 ≤ C.Wd) (a0_valid C)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
  unfold coldCarrierInitialize
  refine (Hs.seq (t1 := 5) (t2 := carrierStartupCost r) hi
    fun a ⟨⟨hc, hram, hrc, hip, hout, hkin, _hkout, _hkc, _hfr⟩, hva⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hin : C.inp.drop a.ip = Greedy.printInput r ++ [] := by
    change a.ip = 0 at hip
    rw [hip, List.drop_zero, List.append_nil]
    rfl
  have haempty : ∀ store, a.ram store = [] ∧ a.rc store = 0 := by
    intro store
    rw [hram, hrc]
    exact ⟨rfl, rfl⟩
  refine (initializeCarrierSource_spec C r [] a hc hva hin hwidth haempty).mono le_rfl ?_
  rintro z ⟨hzo, hzdata, hzinput, hzcallee, hzc, hzvalid⟩
  refine ⟨?_, hzdata, hzinput, ?_, hzc, hzvalid⟩
  · change a.out = [] at hout
    simpa only [hout, List.nil_append] using hzo
  · have hk : z.kin = a.kin := congrArg (fun t => t.1) hzcallee
    exact hk.trans hkin

/-- `lem:print` and `prop:time`, paper/paper.tex: concrete source-callee reservations discharge the
shared eight-mask entry guards from the actual fixed source context. -/
theorem printMasksReady_of_actual_source {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (a : DS VV MM)
    (hresidue : ResidueReady (printSourceContext B1 B2 (Greedy.printInput r)) r a (sourceEnvelope r))
    (hprepared : a.ram preparedStore = (preparedWordOf r).map Bool.toNat)
    (hbytes : a.env preparedLength = (preparedWordOf r).length)
    (hcursor : a.rc preparedStore = (preparedWordOf r).length)
    (hkin : a.kin = []) (hindex : a.env printWalkIndex = index.val) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    PrintMasksReady C.Wd C.inp C.Lk C.Bk r index a := by
  refine ⟨hresidue, hprepared, hbytes, hcursor, hkin, hindex, ?_, ?_⟩
  · intro edge
    change (StageMainMask.structuralWord (printMaskStructuralRequest r index edge)).length ≤
      (printSourceSizes B1 B2).Lk (leadOnes (Greedy.printInput r))
    simpa only [List.append_nil] using (printMask_callee_reserves r index [] edge).1
  · intro edge
    change StageMainMask.structuralBudget (printMaskStructuralRequest r index edge) ≤
      (printSourceSizes B1 B2).Bk (leadOnes (Greedy.printInput r))
    simpa only [List.append_nil] using (printMask_callee_reserves r index [] edge).2

end NearQuarticWires.StageLift
