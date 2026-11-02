import Proof.Quartic.StageGamma.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the complete
ORIGINAL static query state is stored in these fixed binary variables. -/
def staticRegisters : List (Fin VV) :=
  List.ofFn requestFieldRegister ++
    [gammaModulus, gammaRest, gammaCellWidth, gammaSide, gammaBase, gammaCensus] ++
      (List.finRange 8).map gammaCell

/-- `cor:conditional`, paper/paper.tex: all actual
Gaussian source, kernel-call and reply changes leave ORIGINAL static data
and the exact coefficient address untouched. -/
theorem staticRegisters_gauss :
    (∀ x : Fin VV, x ∈ staticRegisters → x ∉ writerScratch ++ replyScratch) ∧
    (∀ slot : Fin 8, gammaDigit slot ∉ writerScratch ++ replyScratch) := by
  constructor
  · decide
  · intro slot
    fin_cases slot <;> decide

/-- `cor:conditional`, paper/paper.tex: retaining
the exact ORIGINAL static registers and input cursor retains the whole
static state, independently of the current Gaussian reply buffer. -/
theorem StaticReady.preserve_registers (request : Machine.GammaRequest) {a b : DS VV MM}
    (ha : StaticReady request a)
    (hr : ∀ x ∈ staticRegisters, b.env x = a.env x)
    (hip : b.ip = a.ip) (hkin : b.kin = []) (hc : Cst b) : StaticReady request b := by
  refine ⟨⟨?_, ?_, hip.trans ha.header.2.2.1, hkin, hc⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hr (requestFieldRegister i) (by
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))]
    exact ha.header.1 i
  · rw [hr gammaModulus (by decide)]
    exact ha.header.2.1
  · rw [hr gammaRest (by decide)]
    exact ha.rest
  · rw [hr gammaCellWidth (by decide)]
    exact ha.cellWidth
  · rw [hr gammaSide (by decide)]
    exact ha.side
  · intro slot
    rw [hr (gammaCell slot) (by
      exact List.mem_append_right _ (List.mem_map.mpr ⟨slot, List.mem_finRange _, rfl⟩))]
    exact ha.cells slot
  · rw [hr gammaBase (by decide)]
    exact ha.base
  · rw [hr gammaCensus (by decide)]
    exact ha.census

/-- `cor:conditional`, paper/paper.tex: the entire
actual coefficient query modifies only decoded-choice and Gaussian scratch. -/
def queryScratch : List (Fin VV) := choiceScratch ++ (writerScratch ++ replyScratch)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the full physical query returns its exact original Gaussian
answer while retaining the complete static state and its true choice digits
for signed coefficient computation and the next ORIGINAL address. -/
theorem gammaQuery_frame (request : Machine.GammaRequest)
    (address : Fin ((request.parameters.Q + 1) ^ 8)) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (ha : StaticReady request a)
    (haddress : a.env gammaAddress = address.val)
    (hwidth : Cycle.seedLength request.parameters + 10 ≤ width) :
    Hs (gaussContext width input (gaussInputReserve request) (gaussWorkReserve request))
      gammaQuery a (2000001 * (Cycle.seedLength request.parameters + 9) ^ 6)
      (fun b =>
        b.env gammaExponent = kernelExponent request (littleChoiceEquiv request.parameters.Q address) ∧
        b.env gammaFlag = (kernelFlag request (littleChoiceEquiv request.parameters.Q address)).toNat ∧
        StaticReady request b ∧
        (∀ slot, b.env (gammaDigit slot) = (littleChoiceEquiv request.parameters.Q address slot).val) ∧
        b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Fr a b queryScratch) := by
  let C := gaussContext width input (gaussInputReserve request) (gaussWorkReserve request)
  refine Hs.mono (Hs.seq (t1 := 77)
    (t2 := 2000000 * (Cycle.seedLength request.parameters + 9) ^ 6)
    (choicePrepare_run C request address a ha haddress hwidth) ?_) ?_ (fun _ h => h)
  · intro b ⟨hbank, hstatic, hs, hfr⟩
    refine Hs.mono (gammaGaussStep_run request (littleChoiceEquiv request.parameters.Q address)
      width input b hstatic.header.2.2.2.2 hbank hstatic.header.2.2.2.1 (by omega)) le_rfl ?_
    intro d ⟨he, hf, hk, hi, ho, hr, hrc, hc, hfd⟩
    have hdstatic := StaticReady.preserve_registers request hstatic
      (fun x hx => hfd x (staticRegisters_gauss.1 x hx)) hi hk hc
    refine ⟨he, hf, hdstatic, ?_, ho.trans hs.out, hr.trans hs.ram, hrc.trans hs.rc,
      (hfr.weaken (fun x hx => List.mem_append_left _ hx)).trans
        (hfd.weaken (fun x hx => List.mem_append_right _ hx))⟩
    intro slot
    rw [hfd _ (staticRegisters_gauss.2 slot)]
    exact hbank.digit slot
  · have hq : 78 ≤ (Cycle.seedLength request.parameters + 9) ^ 6 := by
      have hh : 9 ^ 6 ≤ (Cycle.seedLength request.parameters + 9) ^ 6 :=
        Nat.pow_le_pow_left (by omega) _
      omega
    nlinarith

end NearQuarticWires.StageGamma
