import Proof.Quartic.StageHamming.ColumnSelect

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def columnReadScratch : List (Fin VV) :=
  [bitIndex, bitOutput, bitWork, bitCounter, bitQuotient]

def columnStepScratch : List (Fin VV) :=
  columnOutput :: parityPower :: vJ :: columnReadScratch

/-- `imp:partition`, paper/paper.tex: one check
coordinate is read from the actual data-position number, compared
with the original target, and incorporated into the codeword bit. -/
def columnStep : St VV MM :=
  .seq (.op (.copy bitIndex columnCounter))
    (.seq readScalarBit (.seq columnSelect (.op (.shl parityPower))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the physical codeword-column step realizes the canonical
prefix update, paying its actual binary bit selection and power shift. -/
theorem columnStep_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i q k : ℕ) (hinput : a.env bitInput = i + 1)
    (hsucc : a.env paritySuccessor = q + 1)
    (hcounter : a.env columnCounter = k) (hpower : a.env parityPower = 2 ^ k)
    (hflag : a.env columnOutput = (columnPrefix i q k).toNat)
    (hk : k < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) (hW : 2 ^ (k + 1) < 2 ^ C.Wd) :
    Hs C columnStep a (5 * k + 17) (fun b =>
      b.env parityPower = 2 ^ (k + 1) ∧
      b.env columnOutput = (columnPrefix i q (k + 1)).toNat ∧
      b.sh = a.sh ∧ Fr a b columnStepScratch) := by
  unfold columnStep
  refine Hx.hs (Hs.then (hs_copy C bitIndex columnCounter a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let b := a.set bitIndex (a.env columnCounter)
  have hf0 : Fr a b columnReadScratch := Fr.set _ _ (by simp [columnReadScratch])
  have hcb : Cst b := hc.of_fr hf0 (by decide)
  have hbi : b.env bitInput = i + 1 := (hf0 _ (by decide)).trans hinput
  have hbk : b.env bitIndex = k := (DS.set_env_self _ _ _).trans hcounter
  refine Hs.then (readScalarBit_spec b hcb (by rw [hbk]; exact hk) hwidth)
    (fun c hcp n2 hn2 => ?_)
  obtain ⟨hbit, hsh, hfr⟩ := hcp
  have hf : Fr a c columnReadScratch := hf0.trans (hfr.weaken (by decide))
  have hcc : Cst c := hc.of_fr hf (by decide)
  have hbc : c.env bitOutput = ((i + 1).testBit k).toNat := by
    simpa only [hbi, hbk] using hbit
  refine Hs.then (columnSelect_spec c hcc (q + 1) (2 ^ k)
    (columnPrefix i q k) ((i + 1).testBit k)
    ((hf _ (by decide)).trans hsucc) ((hf _ (by decide)).trans hpower)
    ((hf _ (by decide)).trans hflag) hbc) (fun d hdp n3 hn3 => ?_)
  obtain ⟨hdflag, hdsh, hdfr⟩ := hdp
  have hdpower : d.env parityPower = 2 ^ k :=
    (hdfr _ (by decide)).trans ((hf _ (by decide)).trans hpower)
  refine Hs.last (hs_shl C parityPower d (by
    rw [hdpower, ← pow_succ']; exact hW)) ?_
  rintro e rfl n4 hn4
  refine ⟨⟨?_, ?_, hdsh.trans hsh,
    (hf.weaken (by decide)).trans
      ((hdfr.weaken (by decide)).trans (Fr.set _ _ (by simp [columnStepScratch])))⟩, ?_⟩
  · rw [DS.set_env_self, hdpower, ← pow_succ']
  · rw [DS.set_env_ne _ _ (by decide), columnPrefix_succ]
    exact hdflag
  · rw [hbk] at hn2
    omega

end NearQuarticWires.StageHamming
