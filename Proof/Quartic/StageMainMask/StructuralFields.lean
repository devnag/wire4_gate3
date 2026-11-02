import Proof.Quartic.StageMainMask.SourceSkip
import Proof.Quartic.StageCert.StructuralProgram
import Proof.Quartic.StageOutput.Parse
import Proof.Gates.Dispatch.WitnessB

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Dispatch
open StageCert.Incidence

/-- `def:mask`, paper/paper.tex: the exact scalar
suffix identifies the original heavy-coordinate threshold, block
geometry, and the two canonical star-pattern codes. -/
def structuralFields (P : StarParams) (cut : ℕ)
    (u v : Fin ((P.b + 1) ^ (P.r / 2))) : List (Fin VV × ℕ) :=
  [(heavyThreshold, cut), (patternBlockSize, P.b), (patternCount, P.r),
    (patternLeftInput, u.val), (patternRightInput, v.val)]

def structuralFieldRegisters : List (Fin VV) :=
  [heavyThreshold, patternBlockSize, patternCount, patternLeftInput, patternRightInput]

/-- `def:mask`, paper/paper.tex: the loaded scalar
fields are the concrete inputs of the original-source structural test. -/
structure StructuralLoaded (a : DS VV) (P : StarParams) (cut : ℕ)
    (u v : Fin ((P.b + 1) ^ (P.r / 2))) : Prop where
  threshold : a.env heavyThreshold = cut
  blockSize : a.env patternBlockSize = P.b
  radix : a.env patternRadix = P.b + 1
  count : a.env patternCount = P.r / 2
  left : a.env patternLeftInput = u.val
  right : a.env patternRightInput = v.val

/-- `def:mask`, paper/paper.tex: actual scalar
parsing computes the radix and side count before physically returning
the original-source cursor to zero. -/
def loadStructuralFields : St VV :=
  .seq (StageOutput.readScalars structuralFieldRegisters)
    (.seq (.op (.copy patternRadix patternBlockSize))
      (.seq (.op (.inc patternRadix))
        (.seq (.op (.half patternCount)) (seekW vZ))))

/-- `def:mask` and `prop:time`, paper/paper.tex: the concrete suffix reader initializes every structural
input from actual encoded fields and restores the synchronized source
cursor, rather than assuming an initialized arithmetic environment. -/
theorem loadStructuralFields_spec {C : Ctx} (a : DS VV) (hc : Cst a)
    (P : StarParams) (cut : ℕ) (u v : Fin ((P.b + 1) ^ (P.r / 2)))
    (rest : List Bool)
    (hin : C.cw.drop a.cp = (structuralFields P cut u v).flatMap (fun f => natWord f.2) ++ rest)
    (hW : ∀ f ∈ structuralFields P cut u v, natBitLength f.2 + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (hRadix : P.b + 1 < 2 ^ C.Wd) :
    Hs C loadStructuralFields a
      (StageOutput.readScalarsCost (structuralFields P cut u v) + 16) (fun b =>
        StructuralLoaded b P cut u v ∧ b.cp = 0 ∧ b.wq = a.wq ∧
          b.out = a.out ∧ Cst b) := by
  have hread := StageOutput.readScalars_spec (structuralFields P cut u v)
    (by intro f hf; simp only [structuralFields, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    hW hL rest a hc hin
  unfold loadStructuralFields
  refine Hx.hs (Hs.then hread (fun b hb n1 hn1 => ?_))
  obtain ⟨_hbcp, hbwq, hbout, hbc, hbenv⟩ := hb
  have hcut : b.env heavyThreshold = cut := by
    simpa (config := { decide := true }) [StageOutput.fieldEnv, structuralFields] using
      hbenv heavyThreshold (by decide)
  have hblock : b.env patternBlockSize = P.b := by
    simpa (config := { decide := true }) [StageOutput.fieldEnv, structuralFields] using
      hbenv patternBlockSize (by decide)
  have hcount : b.env patternCount = P.r := by
    simpa (config := { decide := true }) [StageOutput.fieldEnv, structuralFields] using
      hbenv patternCount (by decide)
  have hleft : b.env patternLeftInput = u.val := by
    simpa (config := { decide := true }) [StageOutput.fieldEnv, structuralFields] using
      hbenv patternLeftInput (by decide)
  have hright : b.env patternRightInput = v.val := by
    simpa (config := { decide := true }) [StageOutput.fieldEnv, structuralFields] using
      hbenv patternRightInput (by decide)
  refine Hs.then (hs_copy C patternRadix patternBlockSize b (by decide))
    (fun c hc' n2 hn2 => ?_)
  subst hc'
  let a1 := b.set patternRadix (b.env patternBlockSize)
  refine Hs.then (hs_inc C patternRadix a1 (by rw [DS.set_env_self, hblock]; exact hRadix))
    (fun c hc' n3 hn3 => ?_)
  subst hc'
  let a2 := a1.set patternRadix (a1.env patternRadix + 1)
  refine Hs.then (hs_half C patternCount a2) (fun c hc' n4 hn4 => ?_)
  subst hc'
  let a3 := a2.set patternCount (a2.env patternCount / 2)
  have hc3 : Cst a3 := ((hbc.set _ _ (by decide)).set _ _ (by decide)).set _ _ (by decide)
  have hz : a3.env vZ = 0 := hc3.z
  refine Hs.last (seekW_spec vZ (by decide) (by decide) a3 hc3 0 hz (by omega) (by omega)) ?_
  rintro c ⟨hccp, hcwq, hcout, hcc, hcfr⟩ n5 hn5
  refine ⟨⟨?_, hccp, hcwq.trans hbwq, hcout.trans hbout, hcc⟩, by omega⟩
  constructor
  · rw [hcfr _ (by decide)]
    vsimp [a3, a2, a1, hcut]
  · rw [hcfr _ (by decide)]
    vsimp [a3, a2, a1, hblock]
  · rw [hcfr _ (by decide)]
    vsimp [a3, a2, a1, hblock]
  · rw [hcfr _ (by decide)]
    vsimp [a3, a2, a1, hcount]
  · rw [hcfr _ (by decide)]
    vsimp [a3, a2, a1, hleft]
  · rw [hcfr _ (by decide)]
    vsimp [a3, a2, a1, hright]

end NearQuarticWires.StageMainMask
