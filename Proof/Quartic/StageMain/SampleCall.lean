import Proof.Quartic.StageMain.SampleBounds
import Proof.Quartic.StageMain.SamplePrepare

/-!
# The physical sampler call in the main-pass controller

`imp:seed`, paper/paper.tex, and the main pass: the stored seed is split, encoded into the exact
Horner-bank input, and evaluated by its fixed ordinary machine.
The repeated sample cost contains no primitive-field search.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg
open StageGamma

noncomputable def sampleCallee : Callee :=
  ⟨SampleRequest, sampleRawWord, sampleRawOutput, sampleRawBudget, sampleRawWordFunction⟩

noncomputable def sampleContext (width : ℕ) (input : List Bool) (L B : ℕ) : Ctx :=
  ⟨width, input, sampleCallee, L, B⟩

def sampleInputReserve (ell : ℕ) : ℕ := 10000 * (ell + 1)
def sampleWorkReserve (ell : ℕ) : ℕ := 100000 * (ell + 1) ^ 2

def sampleCall : St VV MM := .seq sampleRecipe.program (.op .kcall)

theorem sampleCall_run (r : SampleRequest) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : SampleStored r a)
    (hkin : a.kin = []) (hwidth : r.ell + 2 ≤ width) :
    Hs (sampleContext width input (sampleInputReserve r.ell) (sampleWorkReserve r.ell))
      sampleCall a (200000 * (r.ell + 1) ^ 2) (fun b =>
        b.kout = sampleRawOutput r ∧ b.kc = 0 ∧ b.kin = [] ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Cst b ∧ Fr a b writerScratch) := by
  let C := sampleContext width input (sampleInputReserve r.ell) (sampleWorkReserve r.ell)
  have hw := sampleRecipe_run r C a hc ha (by dsimp [C, sampleContext]; omega)
    (sampleRecipe_params_fit r a hc ha width hwidth)
    (by simpa [C, sampleContext, hkin, sampleInputReserve] using sampleRecipe_cost r a ha)
  refine Hs.mono (Hs.seq (t1 := sampleRecipe.cost a)
    (t2 := 1 + sampleInputReserve r.ell + sampleWorkReserve r.ell) hw ?_) ?_ (fun _ h => h)
  · intro b ⟨hb, hs, hbc, hfr⟩
    have hin : b.kin = C.K.inw r := by
      simpa only [C, sampleContext, sampleCallee, hkin, List.nil_append] using hb
    have he : Hs C (.op .kcall) b (1 + sampleInputReserve r.ell + sampleWorkReserve r.ell)
        (fun d => d = b.called (sampleRawOutput r)) :=
      Hs.op (OpEx.kcall (C := C) r b hin (sampleRawBudget_le r)) rfl
    refine he.mono le_rfl ?_
    rintro d rfl
    exact ⟨rfl, rfl, rfl, hs.ip, hs.out, hs.ram, hs.rc, ⟨hbc.z, hbc.one, hbc.two⟩, hfr⟩
  · have hcost := sampleRecipe_cost r a ha
    dsimp [sampleInputReserve, sampleWorkReserve]
    nlinarith

def prepareAndSample : St VV MM := .seq samplePrepare sampleCall

theorem prepareAndSample_run (r : SampleRequest) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (hc : Cst a) (hs : a.env seed = r.seed) (he : a.env ell = r.ell)
    (hm : a.env modulus = r.modulus) (hl : a.env label = r.label)
    (hkin : a.kin = []) (hwidth : r.ell + 2 ≤ width) :
    Hs (sampleContext width input (sampleInputReserve r.ell) (sampleWorkReserve r.ell))
      prepareAndSample a (300000 * (r.ell + 1) ^ 2) (fun b =>
        b.kout = sampleRawOutput r ∧ b.kc = 0 ∧ b.kin = [] ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Cst b ∧ Fr a b (preparationScratch ++ writerScratch)) := by
  let C := sampleContext width input (sampleInputReserve r.ell) (sampleWorkReserve r.ell)
  refine Hs.mono (Hs.seq (t1 := 5 * r.ell + 40) (t2 := 200000 * (r.ell + 1) ^ 2)
    (samplePrepare_run r C a hc hs he hm hl hwidth) ?_) (by nlinarith) (fun _ h => h)
  intro b ⟨hb, hsame, hbc, hfr⟩
  refine (sampleCall_run r width input b hbc hb (hsame.kin.trans hkin) hwidth).mono le_rfl ?_
  intro d ⟨hd, hdk, hdkin, hdip, hdout, hdram, hdrc, hdc, hdfr⟩
  refine ⟨hd, hdk, hdkin, hdip.trans hsame.ip, hdout.trans hsame.out,
    hdram.trans hsame.ram, hdrc.trans hsame.rc, hdc, ?_⟩
  exact (hfr.weaken (fun x hx => List.mem_append_left _ hx)).trans
    (hdfr.weaken (fun x hx => List.mem_append_right _ hx))

end NearQuarticWires.StageMain.SampleCells
