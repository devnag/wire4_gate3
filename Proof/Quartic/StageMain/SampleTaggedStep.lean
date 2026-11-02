import Proof.Quartic.StageMain.SampleTaggedCall

/-!
# A decoded sample through the shared ordinary call port

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: cached coefficient registers are used
for the selected label, and the framed field answer is read completely.
The coefficients and all original source and output streams are retained.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open StageGamma

variable {Req : Type} {rightInput rightOutput : Req → List Bool} {rightBudget : Req → ℕ}

def taggedSampleStep : St VV MM := .seq taggedSampleCall readSampleReply

def cachedSampleScratch : List (Fin VV) := writerScratch ++ sampleReplyScratch

theorem taggedSampleStep_run
    (f : WordFunction Req rightInput (fun r => frame (rightOutput r)) rightBudget)
    (r : SampleRequest) (width : ℕ) (input : List Bool) (L B : ℕ)
    (a : DS VV MM) (hc : Cst a) (ha : SampleStored r a)
    (hkin : a.kin = []) (hwidth : r.ell + 2 ≤ width)
    (hL : 10000 * (r.ell + 1) + 1 ≤ L)
    (hB : 30000000 * (r.ell + 1) ^ 2 ≤ B) :
    Hs (taggedContext width input f L B) taggedSampleStep a
      (2 * L + B + 12 * r.ell + 21) (fun b =>
        b.env sampleValue = JoinElimination.gen r.modulus r.ell 8 r.seed r.label ∧
        b.kc = 2 * r.ell + 1 ∧ b.kout = sampleRawOutput r ∧ b.kin = [] ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Cst b ∧ Fr a b cachedSampleScratch) := by
  let C := taggedContext width input f L B
  refine Hs.mono (Hs.seq (t1 := 2 * L + B + 10) (t2 := 12 * r.ell + 10)
    (taggedSampleCall_run f r width input L B a hc ha hkin hwidth hL hB) ?_)
    (by omega) (fun _ h => h)
  intro b ⟨hbo, hbk, hbkin, hbip, hbout, hbram, hbrc, hbc, hbfr⟩
  have hbe : b.env ell = r.ell := (hbfr ell (by decide)).trans ha.degree
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

theorem cachedSample_keeps_coefficients (r : SampleRequest) (a b : DS VV MM)
    (ha : SampleStored r a) (hfr : Fr a b cachedSampleScratch) : SampleStored r b := by
  refine ⟨(hfr ell (by decide)).trans ha.degree,
    (hfr modulus (by decide)).trans ha.field,
    (hfr label (by decide)).trans ha.sampleLabel, ?_⟩
  intro i
  have hi : coefficient i ∉ cachedSampleScratch := by
    fin_cases i <;> decide
  exact (hfr (coefficient i) hi).trans (ha.coeff i)

end NearQuarticWires.StageMain.SampleCells
