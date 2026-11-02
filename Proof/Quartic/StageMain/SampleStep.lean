import Proof.Quartic.StageMain.SampleReply
import Proof.Quartic.StageMain.ActualSample

/-!
# One complete field sample in the main-pass controller

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: coefficient preparation, polynomial
execution and full binary decoding produce the actual seeded position.
The stored modulus and the original input and output streams are preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open StageGamma

def sampleStep : St VV MM := .seq prepareAndSample readSampleReply

def sampleStepScratch : List (Fin VV) :=
  preparationScratch ++ writerScratch ++ sampleReplyScratch

theorem sampleStep_run (r : SampleRequest) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (hc : Cst a) (hs : a.env seed = r.seed) (he : a.env ell = r.ell)
    (hm : a.env modulus = r.modulus) (hl : a.env label = r.label)
    (hkin : a.kin = []) (hwidth : r.ell + 2 ≤ width) :
    Hs (sampleContext width input (sampleInputReserve r.ell) (sampleWorkReserve r.ell))
      sampleStep a (400000 * (r.ell + 1) ^ 2) (fun b =>
        b.env sampleValue = JoinElimination.gen r.modulus r.ell 8 r.seed r.label ∧
        b.kc = 2 * r.ell + 1 ∧ b.kout = sampleRawOutput r ∧ b.kin = [] ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Cst b ∧ Fr a b sampleStepScratch) := by
  let C := sampleContext width input (sampleInputReserve r.ell) (sampleWorkReserve r.ell)
  refine Hs.mono (Hs.seq (t1 := 300000 * (r.ell + 1) ^ 2) (t2 := 12 * r.ell + 10)
    (prepareAndSample_run r width input a hc hs he hm hl hkin hwidth) ?_)
    (by nlinarith) (fun _ h => h)
  intro b ⟨hbo, hbk, hbkin, hbip, hbout, hbram, hbrc, hbc, hbfr⟩
  have hbe : b.env ell = r.ell := (hbfr ell (by decide)).trans he
  have hlt := (Sampler.gen_spec r.modulus r.ell r.seed r.label r.modulus_ok
    r.positive r.label_lt 8).1
  refine (readSampleReply_run C b hbc r.ell
    (JoinElimination.gen r.modulus r.ell 8 r.seed r.label) hbe hwidth hlt hbo hbk).mono le_rfl ?_
  intro d ⟨hdv, hdk, hdf, hdc, hdfr⟩
  refine ⟨hdv, hdk, hdf.kout.trans hbo, hdf.kin.trans hbkin,
    hdf.ip.trans hbip, hdf.out.trans hbout, hdf.ram.trans hbram,
    hdf.rc.trans hbrc, hdc, ?_⟩
  exact (hbfr.weaken (fun x hx => List.mem_append_left _ hx)).trans
    (hdfr.weaken (fun x hx => List.mem_append_right _ hx))

theorem selectedSampleStep_run (P : Sampler.SeedParams) (chosen : ℕ) (j : Fin P.Q)
    (width : ℕ) (input : List Bool) (a : DS VV MM) (hc : Cst a)
    (hs : a.env seed = chosen) (he : a.env ell = P.ell)
    (hm : a.env modulus = P.modulus) (hl : a.env label = j.val)
    (hkin : a.kin = []) (hwidth : P.ell + 2 ≤ width) :
    Hs (sampleContext width input (sampleInputReserve P.ell) (sampleWorkReserve P.ell))
      sampleStep a (400000 * (P.ell + 1) ^ 2) (fun b =>
        P.cellEquiv (fun q => GF.bitF ((b.env sampleValue).testBit q)) =
          Cycle.seedSample P chosen j ∧
        b.kc = 2 * P.ell + 1 ∧ b.kin = [] ∧ b.ip = a.ip ∧ b.out = a.out ∧
        b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧ Fr a b sampleStepScratch) := by
  refine (sampleStep_run (actualSampleRequest P chosen j) width input a hc
    hs he hm hl hkin hwidth).mono le_rfl ?_
  intro b ⟨hbv, hbk, _, hbkin, hbip, hbout, hbram, hbrc, hbc, hbfr⟩
  refine ⟨?_, hbk, hbkin, hbip, hbout, hbram, hbrc, hbc, hbfr⟩
  rw [hbv]
  exact (actualSamplePosition P chosen j).symm

end NearQuarticWires.StageMain.SampleCells
