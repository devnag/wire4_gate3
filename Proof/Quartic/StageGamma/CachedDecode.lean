import Proof.Quartic.StageGamma.FixedRead
import Proof.Quartic.StageGamma.FieldBudget
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- `imp:seed`, paper/paper.tex: the primitive
modulus consists of the physically cached low bits and its monic top bit. -/
theorem primitive_modulus_low_add (request : Machine.GammaRequest) :
    request.parameters.modulus % 2 ^ request.parameters.ell +
      2 ^ request.parameters.ell = request.parameters.modulus := by
  have hp := request.parameters.cert.2.1
  have hbit : request.parameters.modulus / 2 ^ request.parameters.ell % 2 = 1 := by
    have hh := hp.1
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff] at hh
    exact hh
  have hdiv : request.parameters.modulus / 2 ^ request.parameters.ell < 2 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa [pow_succ, Nat.mul_comm] using hp.2
  have he : request.parameters.modulus / 2 ^ request.parameters.ell = 1 := by
    rwa [Nat.mod_eq_of_lt hdiv] at hbit
  have hh := Nat.mod_add_div request.parameters.modulus (2 ^ request.parameters.ell)
  simpa [he] using hh

/-- `imp:seed`, paper/paper.tex: decode the cached
low bits and physically install the primitive polynomial's monic bit. -/
def readCachedModulus : St VV MM :=
  .seq (fixedRead (requestFieldRegister 0) gammaModulus) (.op (.add gammaModulus t1))

/-- `imp:seed` and `prop:time`, paper/paper.tex: the actual field cache is decoded in linear degree time; all
ORIGINAL request registers remain available for every Gaussian choice. -/
theorem readCachedModulus_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp = cachedRequestWord request)
    (hip : a.ip = (Machine.gammaRequestWord request).length)
    (hell : a.env (requestFieldRegister 0) = request.parameters.ell)
    (hwidth : request.parameters.ell + 2 ≤ C.Wd) :
    Hs C readCachedModulus a (10 * request.parameters.ell + 20) (fun b =>
      b.env gammaModulus = request.parameters.modulus ∧
      b.ip = (cachedRequestWord request).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (fixedReadScratch gammaModulus)) := by
  have hp : request.parameters.modulus < 2 ^ C.Wd :=
    request.parameters.cert.2.1.2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hread := fixedRead_run C (requestFieldRegister 0) gammaModulus (by decide) (by decide)
    a hc request.parameters.ell request.parameters.modulus [] hell (by omega)
    (by simp [hin, hip, cachedRequestWord])
  refine Hs.seq (t1 := 10 * request.parameters.ell + 18) (t2 := 1) hread ?_
  intro b ⟨hb, ht1, hbi, hrest, hbc, hfr⟩
  refine Hs.mono (hs_add C gammaModulus t1 b (by decide)
    (by rw [hb, ht1, primitive_modulus_low_add]; exact hp)) le_rfl ?_
  rintro d rfl
  refine ⟨by rw [DS.set_env_self, hb, ht1, primitive_modulus_low_add], ?_, hrest,
    Cst.of_fr (T := fixedReadScratch gammaModulus) hbc
      (Fr.set b _ (by simp [fixedReadScratch])) (by decide),
    hfr.trans (Fr.set b _ (by simp [fixedReadScratch]))⟩
  simp only [DS.set_ip, cachedRequestWord, List.length_append, SignedSortKey.binary_length]
  omega

/-- `cor:conditional`, paper/paper.tex: the actual
cached source begins with exactly the ORIGINAL fourteen request values. -/
def CachedHeader (request : Machine.GammaRequest) (a : DS VV MM) : Prop :=
  (∀ i : Fin 14, a.env (requestFieldRegister i) =
    (requestFields request)[i.val]'(by rw [requestFields_length]; exact i.isLt)) ∧
  a.env gammaModulus = request.parameters.modulus ∧
  a.ip = (cachedRequestWord request).length ∧ a.kin = [] ∧ Cst a

/-- `cor:conditional`, paper/paper.tex: finite
second-stage control starts with real constant initialization, ORIGINAL
request parsing and actual cached-modulus decoding. -/
def cachedHeaderProgram : St VV MM :=
  .seq initP (.seq requestFieldsProgram readCachedModulus)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the second Gaussian stage obtains its whole ORIGINAL header
and cached field from the actual retained source, with no supplied bank. -/
theorem cachedHeaderProgram_run (C : Ctx) (request : Machine.GammaRequest)
    (hin : C.inp = cachedRequestWord request)
    (hwidth : Cycle.seedLength request.parameters + 3 ≤ C.Wd) :
    Hs C cachedHeaderProgram (a0 : DS VV MM)
      (500 * (Cycle.seedLength request.parameters + 9)) (CachedHeader request) := by
  have hell : request.parameters.ell ≤ Cycle.seedLength request.parameters := by
    dsimp [Cycle.seedLength]
    omega
  have h4 : 2 < 2 ^ C.Wd := by
    have htwo : 2 ≤ C.Wd := by omega
    have hh : 4 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (n := 2) (by decide) htwo
    omega
  unfold cachedHeaderProgram
  refine Hs.mono (Hs.seq (t1 := 5)
    (t2 := 420 * Cycle.seedLength request.parameters + 883 +
      (10 * request.parameters.ell + 20) + 1)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl h4) ?_)
    (by omega) (fun _ h => h)
  intro b ⟨hc, _, _, hip, _, hkin, _, _, _⟩
  have hparse := Hs.mono (requestFields_parse_cached C request hin hwidth b hc hip)
    (requestFieldsCost_le request) (fun _ h => h)
  refine Hs.seq (t1 := 420 * Cycle.seedLength request.parameters + 883)
    (t2 := 10 * request.parameters.ell + 20) hparse ?_
  intro d ⟨hfields, hdi, hrest, hdc⟩
  have hdell : d.env (requestFieldRegister 0) = request.parameters.ell := by
    simpa [requestFields] using hfields 0
  refine Hs.mono (readCachedModulus_run C request d hdc hin hdi hdell (by omega)) le_rfl ?_
  intro e ⟨he, hei, herest, hec, hefr⟩
  refine ⟨?_, he, hei, ?_, hec⟩
  · intro i
    rw [hefr (requestFieldRegister i) (by
      fin_cases i <;> decide)]
    exact hfields i
  · have hdk : d.kin = b.kin := by
      have hh := congrArg (fun t => t.2.2.2.1) hrest
      exact hh
    have hek : e.kin = d.kin := by
      exact congrArg (fun t => t.2.2.2.1) herest
    rw [hek, hdk, hkin]
    rfl

end NearQuarticWires.StageGamma
