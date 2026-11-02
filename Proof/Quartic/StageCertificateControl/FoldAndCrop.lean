import Proof.Quartic.StageCertificateControl.InitializeFold
import Proof.Quartic.StageCertificateControl.CropFold

/-!
# The complete signed test-major bitmap computation

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageRecovery (countVar)

/-- The full bitmap computation in `sec:algorithm`,
paper/paper.tex, initializes once, conjoins every
whole signed table, and crops only after the last test. -/
def foldAndCrop (first second : Fin MM) : St VV MM :=
  .seq (initializeFold first second) (.seq (testFold first second) (cropFold first second))

/-- The actual complete bitmap computation of `sec:algorithm` and
`prop:time`, paper/paper.tex,
constructs its arrays from empty stores. All signed native columns
participate in every strict test before the sole final prefix scan. -/
theorem foldAndCrop_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (first second : Fin MM) (hstores : first≠second)
    (tests : List NativeTest) (count keep : ℕ) (rest : List Bool)
    (htests : ∀ test∈tests, test.values.length=count)
    (hin : C.inp.drop a.ip=nativeTestStream tests++rest)
    (hn : a.env countVar=count) (hnfit : count<2^C.Wd)
    (htestCount : a.env testCountVar=tests.length) (htestFit : tests.length<2^C.Wd)
    (hk : a.env keepVar=keep) (hkeep : keep≤count)
    (hvalues : ∀ test∈tests, ∀ z∈test.values, encS z<2^test.width)
    (hwidth : ∀ test∈tests, test.width+2≤C.Wd)
    (hboundWord : ∀ test∈tests, natBitLength test.bound+2≤C.Wd)
    (hwidthWord : ∀ test∈tests, natBitLength test.width+2≤C.Wd) (hfour : 4≤2^C.Wd)
    (hfirst : a.ram first=[]) (hsecond : a.ram second=[])
    (hri : a.rc first=0) (hro : a.rc second=0) :
    Hs C (foldAndCrop first second) a (testFoldCost tests+21*count+24) (fun b =>
      b.out=a.out++frame ((nativeTestFlags tests (List.replicate count true)).take keep)) := by
  unfold foldAndCrop
  refine (Hs.seq (t2 := testFoldCost tests+(count+10*keep+11)+1)
    (initializeFold_spec C a hc first second hstores count hn hnfit hfirst hsecond hri hro)
    fun b ⟨hbm,hbr,hbc,hbs,hcc,hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbcount : b.env countVar=count := (hbf _ (by decide)).trans hn
  have hbtest : b.env testCountVar=tests.length := (hbf _ (by decide)).trans htestCount
  have hbi : b.ip=a.ip := congrArg Prod.fst hbs
  have hbool : (List.replicate count true).map Bool.toNat=List.replicate count 1 := by simp
  refine Hs.seq
    (testFold_spec C b hcc first second hstores false hbm tests (List.replicate count true) count rest
      htests (by simp) (by rw [hbi];exact hin) hbcount hnfit hbtest htestFit
      hvalues hwidth hboundWord hwidthWord hfour
      (by simp [activeStore,hbr,hstores,hbool])
      (by simp [activeStore,hbr])
      (by simp [hbc,hstores]) (by simp [hbc]))
    fun d ⟨mode,hdm,hdf,hdo,hdrc,_,_,_,hds,hdc,hdfr⟩ => ?_
  have hlen : (nativeTestFlags tests (List.replicate count true)).length=count :=
    nativeTestFlags_length tests _ count htests (by simp)
  have hcursor : d.rc (activeStore first second mode)=count := by
    rw [hdrc,hbc]
    cases mode <;> simp [activeStore,hstores]
  have hdcrop : Hs C (cropFold first second) d (count+10*keep+11)
      (fun e => e.out=d.out++frame ((nativeTestFlags tests (List.replicate count true)).take keep) ∧ Cst e) := by
    simpa only [hlen] using cropFold_spec C d hdc first second mode hdm
      (nativeTestFlags tests (List.replicate count true)) keep
      (by rw [hlen];exact hkeep)
      ((hdfr _ (by decide)).trans ((hbf _ (by decide)).trans hk))
      (Nat.lt_of_le_of_lt hkeep hnfit) hdf (by rw [hlen];exact hcursor)
  refine hdcrop.mono le_rfl ?_
  rintro e ⟨heo,_⟩
  have hdo' : d.out=b.out := congrArg Prod.fst hds
  have hbo : b.out=a.out := congrArg (fun q => q.2.1) hbs
  rw [heo,hdo',hbo]

end NearQuarticWires.StageCertificateControl
