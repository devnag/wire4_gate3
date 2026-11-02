import Proof.Quartic.StageGamma.BankBounds

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the actual
per-choice coefficient control writes the full compact Gaussian source,
calls its physical machine, and decodes its exact flag and nullity. -/
def gammaGaussStep : St VV MM := .seq gammaGaussCall readGaussReply

/-- `prop:time`, paper/paper.tex: the repeated
kernel input reserve is linear in S and contains no field-label census. -/
def gaussInputReserve (request : Machine.GammaRequest) : ℕ :=
  100000 * (Cycle.seedLength request.parameters + 1)

/-- `prop:time`, paper/paper.tex: the repeated
kernel clock is polynomial in S and excludes the once-only field search. -/
def gaussWorkReserve (request : Machine.GammaRequest) : ℕ :=
  1000000 * (Cycle.seedLength request.parameters + 9) ^ 6

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one complete actual Gaussian source-language step has
all source length, width and call-budget premises discharged from the
ORIGINAL request. The cached modulus remains part of the explicit state. -/
theorem gammaGaussStep_run (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : BankReady request choice a)
    (hkin : a.kin = []) (hwidth : Cycle.seedLength request.parameters + 1 ≤ width) :
    Hs (gaussContext width input (gaussInputReserve request) (gaussWorkReserve request))
      gammaGaussStep a (2000000 * (Cycle.seedLength request.parameters + 9) ^ 6)
      (fun b => b.env gammaExponent = kernelExponent request choice ∧
        b.env gammaFlag = (kernelFlag request choice).toNat ∧
        b.kin = [] ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Cst b ∧ Fr a b (writerScratch ++ replyScratch)) := by
  let C := gaussContext width input (gaussInputReserve request) (gaussWorkReserve request)
  have hW : 2 ≤ width := by
    have hh := request.parameters.one_le_ell
    dsimp [Cycle.seedLength] at hwidth
    omega
  have he : kernelExponent request choice ≤ Cycle.seedLength request.parameters := by
    dsimp [kernelExponent, Cycle.seedLength]
    omega
  have hfit : kernelExponent request choice < 2 ^ width := by
    have hs : Cycle.seedLength request.parameters < width := by omega
    exact (he.trans_lt hs).trans (show width < 2 ^ width from Nat.lt_two_pow_self)
  have hcall := gammaGaussCall_run request choice width input (gaussInputReserve request)
    (gaussWorkReserve request) a hc hW ha hkin
    (gammaBankWriter_params_fit request choice a hc ha width hwidth)
    (gammaBankWriter_cost_le_numeric request choice a ha)
    (compactGaussCost_le ⟨request, choice⟩)
  refine Hs.mono (Hs.seq
    (t1 := gammaBankWriter.cost a + (1 + gaussInputReserve request + gaussWorkReserve request) + 1)
    (t2 := 5 * kernelExponent request choice + 8) hcall ?_) ?_ (fun _ h => h)
  · intro b ⟨hbo, hbk, hbkin, hbip, hbout, hbram, hbrc, hbc, hfr⟩
    refine Hs.mono (readGaussReply_run C b hbc (kernelExponent request choice)
      (kernelFlag request choice) hbo hbk hfit) le_rfl ?_
    intro d ⟨hde, hdf, _, hs, hdc, hfrd⟩
    exact ⟨hde, hdf, hs.kin.trans hbkin, hs.ip.trans hbip, hs.out.trans hbout,
      hs.ram.trans hbram, hs.rc.trans hbrc, hdc,
      (hfr.weaken (fun x hx => List.mem_append_left _ hx)).trans
        (hfrd.weaken (fun x hx => List.mem_append_right _ hx))⟩
  · have hw := gammaBankWriter_cost_le_numeric request choice a ha
    have hq : Cycle.seedLength request.parameters + 1 ≤
        (Cycle.seedLength request.parameters + 9) ^ 6 := by
      calc
        _ ≤ Cycle.seedLength request.parameters + 9 := by omega
        _ = (Cycle.seedLength request.parameters + 9) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
    dsimp [gaussInputReserve, gaussWorkReserve]
    nlinarith

end NearQuarticWires.StageGamma
