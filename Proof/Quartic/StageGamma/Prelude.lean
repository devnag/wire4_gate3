import Proof.Quartic.StageGamma.ChoicePrepare
import Proof.Quartic.StageGamma.GaussStep

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: complete
physical initialization starts from the retained ORIGINAL source and
computes all choice-independent Gaussian data before enumeration. -/
def gammaPrelude : St VV MM := .seq cachedHeaderProgram staticPrepare

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the complete cached Gaussian prelude physically derives
every static input from the retained ORIGINAL request at linear source cost. -/
theorem gammaPrelude_run (C : Ctx) (request : Machine.GammaRequest)
    (hin : C.inp = cachedRequestWord request)
    (hwidth : Cycle.seedLength request.parameters + 10 ≤ C.Wd) :
    Hs C gammaPrelude (a0 : DS VV MM)
      (600 * (Cycle.seedLength request.parameters + 9)) (StaticReady request) := by
  have hk : request.parameters.kh ≤ Cycle.seedLength request.parameters := by
    have hh := request.parameters.k_le
    dsimp [Cycle.seedLength]
    omega
  refine Hs.mono (Hs.seq
    (t1 := 500 * (Cycle.seedLength request.parameters + 9))
    (t2 := 5 * request.parameters.kh + 121)
    (cachedHeaderProgram_run C request hin (by omega)) ?_) (by omega) (fun _ h => h)
  intro b hb
  exact Hs.mono (staticPrepare_run C request b hb hwidth) le_rfl (fun _ h => h.1)

/-- `cor:conditional`, paper/paper.tex: a complete
coefficient query computes its true choice data before writing, invoking
and reading the actual Gaussian system. -/
def gammaQuery : St VV MM := .seq choicePrepare gammaGaussStep

/-- `cor:conditional` and `prop:time`, paper/paper.tex: every actual original coefficient address has its full
bank and Gaussian answer physically computed with a polynomial seed clock;
there is no externally supplied per-choice bank or repeated field search. -/
theorem gammaQuery_run (request : Machine.GammaRequest)
    (address : Fin ((request.parameters.Q + 1) ^ 8)) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (ha : StaticReady request a)
    (haddress : a.env gammaAddress = address.val)
    (hwidth : Cycle.seedLength request.parameters + 10 ≤ width) :
    Hs (gaussContext width input (gaussInputReserve request) (gaussWorkReserve request))
      gammaQuery a (2000001 * (Cycle.seedLength request.parameters + 9) ^ 6)
      (fun b =>
        b.env gammaExponent = kernelExponent request (littleChoiceEquiv request.parameters.Q address) ∧
        b.env gammaFlag = (kernelFlag request (littleChoiceEquiv request.parameters.Q address)).toNat ∧
        b.kin = [] ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b) := by
  let C := gaussContext width input (gaussInputReserve request) (gaussWorkReserve request)
  have hp := choicePrepare_run C request address a ha haddress hwidth
  refine Hs.mono (Hs.seq (t1 := 77)
    (t2 := 2000000 * (Cycle.seedLength request.parameters + 9) ^ 6) hp ?_) ?_ (fun _ h => h)
  · intro b ⟨hbank, hstatic, hs, _⟩
    refine Hs.mono (gammaGaussStep_run request (littleChoiceEquiv request.parameters.Q address)
      width input b hstatic.header.2.2.2.2 hbank hstatic.header.2.2.2.1 (by omega)) le_rfl ?_
    intro d ⟨he, hf, hk, hi, ho, hr, hrc, hc, _⟩
    exact ⟨he, hf, hk, hi.trans hs.ip, ho.trans hs.out, hr.trans hs.ram, hrc.trans hs.rc, hc⟩
  · have hq : 78 ≤ (Cycle.seedLength request.parameters + 9) ^ 6 := by
      have hp : 9 ^ 6 ≤ (Cycle.seedLength request.parameters + 9) ^ 6 :=
        Nat.pow_le_pow_left (by omega) _
      omega
    nlinarith

end NearQuarticWires.StageGamma
