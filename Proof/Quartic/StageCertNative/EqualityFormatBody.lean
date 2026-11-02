import Proof.Quartic.StageCertNative.EqualityRead
import Proof.Quartic.StageCertNative.EqualityFields

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells
open StagePrint StagePrint.EntryFormat

/-- `lem:print`, paper/paper.tex: after exact
Tuple construction, the original entry source computes the equality
header and copies that term's complete actual signed raw stream. -/
def equalityFormatBody : St VV MM :=
  .seq (readerProgram false) (.seq computeEqualityDimension emitEqualityFields)

noncomputable def equalityFormatSteps (r : Request false) (raw : List Bool) : ℕ :=
  readerSteps r+11*raw.length+9*((r.header.call.n+1)/2)+9*r.termRequest.stackWidth+60

theorem equalityFormatBody_run (C : Ctx) (r : Request false) (raw : List Bool)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=r.word++frame raw)
    (hblank : ∀ s,a.ram s=[] ∧ a.rc s=0) (hfit : InputFits C r) :
    Hs C equalityFormatBody a (equalityFormatSteps r raw) (fun z=>
      z.out=a.out++Top.loadRec raw (List.replicate ((r.header.call.n+1)/2) true)
        (List.replicate r.termRequest.stackWidth true) [] [] [] [] [] [] [] []) := by
  have hn : r.header.call.n+1<2^C.Wd := by
    have hh:=hfit.headerArithmetic
    omega
  have hw : r.termRequest.stackWidth<2^C.Wd := by
    have hh:=hfit.packingArithmetic
    rw [r.stackWidth_actual]
    unfold NativeWidth.packedBits
    omega
  unfold equalityFormatBody
  refine Hx.hs (Hs.then (readEqualityPrefix_run C r (frame raw) a hc hin hblank hfit) ?_)
  rintro b ⟨bn,bw,bin,bo,bc⟩ n0 hn0
  refine Hs.then (computeEqualityDimension_run C r.header.call.n b bc bn hn) ?_
  rintro d ⟨dw,ds,dc,dfr⟩ n1 hn1
  have dip : d.ip=b.ip := congrArg Prod.fst ds
  have din : C.inp.drop d.ip=frame raw := by
    rw [dip]
    exact bin
  have dwidth : d.env GreedyEntry.widthVar=r.termRequest.stackWidth := (dfr _ (by decide)).trans bw
  refine Hs.last (emitEqualityFields_run C raw ((r.header.call.n+1)/2) r.termRequest.stackWidth
    d dc din dw dwidth ((Nat.div_le_self _ _).trans_lt hn) hw) ?_
  rintro z zo n2 hn2
  have doo : d.out=b.out := congrArg (fun q=>q.2.1) ds
  refine ⟨?_,by unfold equalityFormatSteps;omega⟩
  rw [zo,doo,bo]

end NearQuarticWires.StageCertNative
