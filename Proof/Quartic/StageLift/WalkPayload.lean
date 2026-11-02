import Proof.Quartic.StageLift.WalkHead
import Proof.Quartic.StageLift.ColdStartup
import Proof.Quartic.StageLift.SourceWalkShape
import Proof.Quartic.StageLiftMasks.Final
import Proof.Quartic.StageLiftTokens.Final

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the actual
original walk payload writes the split coefficient, eight real-source
tuple masks, the amplified residue body and its two product tokens. -/
def emitWalkPayload : St VV MM :=
  .seq emitWalkHead (.seq StageLiftMasks.printMasksProgram
    (.seq StageLiftTokens.residueBodyProgram (emitLiteral (tokWord .mul ++ tokWord .mul))))

/-- `prop:time`, paper/paper.tex: all source
calls, tuple enumeration, original residue replays and final token
writes contribute to the actual per-walk construction clock. -/
noncomputable def walkPayloadCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (L B : ℕ) : ℕ :=
  walkHeadCost r + printMasksCost r L B + 10 ^ 12 * (sourceEnvelope r + 1) ^ 30 + 100

/-- `lem:print` and Step 3, paper/paper.tex: the complete original payload is physically synthesized
from the actual retained source. Both mask and residue programs are
concrete proved programs; no Formula word or target-body premise is
an additional machine input. -/
theorem emitWalkPayload_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (a : DS VV MM)
    (ha : WalkSourceState (printSourceContext B1 B2 (Greedy.printInput r)) r index.val a)
    (hi : a.env printWalkIndex = index.val) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    Hs C emitWalkPayload a (walkPayloadCost r C.Lk C.Bk) (fun z =>
      z.out = a.out ++ (toks (sourceWalkFormula r index)).flatMap tokWord ∧
      WalkSourceState C r (index.val + 1) z ∧ z.env printWalkIndex = index.val ∧ z.ip = a.ip) := by
  dsimp only
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  have hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd := by
    change _ ≤ (printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r))
    simpa only [List.append_nil] using printSourceSizes_width r []
  obtain ⟨b, nb, heb, hnb, hbo, hbstate, hbready, hbI, hbip⟩ := emitWalkHead_spec C r index a ha hi hW
  have hbmask := printMasksReady_of_actual_source r index b hbready hbstate.sources.preparedBits
    hbstate.sources.preparedBytes hbstate.sources.preparedCursor hbstate.inputEmpty hbI
  have hm := StageLiftMasks.printMasksProgram_run C.Wd C.inp C.Lk C.Bk r index b hbmask
  change Hs C StageLiftMasks.printMasksProgram b (printMasksCost r C.Lk C.Bk) _ at hm
  obtain ⟨c, nc, hec, hnc, hco, hcram, hcrc, hcip, hckin, hcready, hcfields⟩ := hm
  have hcframe : ∀ x ∈ sourceHeaderRegisters, c.env x = b.env x := by
    have hd : ∀ x : Fin VV, x ∈ sourceHeaderRegisters →
        x ∈ ([54,55,56,57,58,59,60,63,71,72,76,96,127] : List (Fin VV)) := by decide
    intro x hx
    exact hcfields x (hd x hx)
  have hcstate := hbstate.of_frame hcram hcframe
    ((hcrc _ (by decide)).trans hbstate.gammaCursor) (hcrc _ (by decide))
    hcready.constants hcready.valid hckin
  have hcI : c.env printWalkIndex = index.val := (hcfields _ (by decide)).trans hbI
  obtain ⟨d, nd, hed, hnd, ⟨hdo, hdram, hdrc, hdstreams, hdc, hdvalid, hdfields⟩, hdP⟩ :=
    StageLiftTokens.residueBodyProgram_run_withCache C r c (sourceEnvelope r) hcready
  have hdframe : ∀ x ∈ sourceHeaderRegisters, d.env x = c.env x := by
    have hd : ∀ x : Fin VV, x ∈ sourceHeaderRegisters → x ≠ preparedLength →
        x ∈ ([54,55,56,57,58,59,60,63,71,72,96,127] : List (Fin VV)) := by decide
    intro x hx
    by_cases hxp : x = preparedLength
    · subst x
      exact hdP
    · exact hdfields x (hd x hx hxp)
  have hdkin : d.kin = [] := (congrArg (fun t => t.2.1) hdstreams).trans hckin
  have hdstate := hcstate.of_frame hdram hdframe
    ((hdrc _ (by decide)).trans hcstate.gammaCursor) (hdrc _ (by decide)) hdc hdvalid hdkin
  have hdI : d.env printWalkIndex = index.val := (hdfields _ (by decide)).trans hcI
  have hsmall : 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.pow_pos (by omega)
  have hop := StagePrint.source_addValid (by omega : 1 ≤ C.Wd) hdvalid
    (emitLiteral_spec C (tokWord .mul ++ tokWord .mul) d hdc)
  obtain ⟨z,nz,hez,hnz,⟨hzo,hzrest,hzc,hzfr⟩,hzvalid⟩ := hop
  have hzram : z.ram = d.ram := congrArg (fun t => t.2.1) hzrest
  have hzrc : z.rc = d.rc := congrArg (fun t => t.2.2.1) hzrest
  have hzkin : z.kin = [] := (congrArg (fun t => t.2.2.2.1) hzrest).trans hdkin
  have hzframe : ∀ x ∈ sourceHeaderRegisters, z.env x = d.env x := by
    have hd : ∀ x : Fin VV, x ∈ sourceHeaderRegisters → x ∉ [vJ] := by decide
    intro x hx
    exact hzfr x (hd x hx)
  have hzstate := hdstate.of_frame hzram hzframe (by rw [hzrc]; exact hdstate.gammaCursor)
    (by rw [hzrc]) hzc hzvalid hzkin
  have hzI : z.env printWalkIndex = index.val := (hzfr _ (by decide)).trans hdI
  have hzip : z.ip = d.ip := congrArg (fun t => t.1) hzrest
  have hdip : d.ip = c.ip := congrArg (fun t => t.1) hdstreams
  refine ⟨z, nb + (nc + (nd + nz + 1) + 1) + 1,
    Ex.seq heb (Ex.seq hec (Ex.seq hed hez)), ?_, ?_, hzstate, hzI,
    hzip.trans (hdip.trans (hcip.trans hbip))⟩
  · have hlen : (tokWord Tok.mul ++ tokWord Tok.mul).length = 14 := by decide
    rw [hlen] at hnz
    change nb + (nc + (nd + nz + 1) + 1) + 1 ≤
      walkHeadCost r + printMasksCost r C.Lk C.Bk + 10 ^ 12 * (sourceEnvelope r + 1) ^ 30 + 100
    omega
  · rw [hzo, hdo, hco, hbo, sourceWalkFormula_tokens]
    simp only [List.append_assoc]

end NearQuarticWires.StageLift
