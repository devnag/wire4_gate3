import Proof.Quartic.StageLift.PreparedCache
import Proof.Quartic.StageRecovery.InputReturn

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `lem:print`, paper/paper.tex: rewind only the physically measured small preparation
word, before any Gamma or arbitrary raw-index source is consumed. -/
def returnPreparedInput : St VV MM :=
  .seq (.op (.copy StageRecovery.tokenLengthVar preparedLength)) StageRecovery.inputReturnProgram

/-- Step 3 and `lem:print`, paper/paper.tex: the actual byte counter pays every input-head return,
with all retained source data and cursors preserved exactly. -/
theorem returnPreparedInput_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (L base : ℕ) (hlen : a.env preparedLength = L) (hip : a.ip = base + L)
    (hfit : L < 2 ^ C.Wd) :
    Hs C returnPreparedInput a (5 * L + 6) (fun b =>
      b.ip = base ∧ StageRecovery.inputRest b = StageRecovery.inputRest a ∧
      b.env preparedLength = L ∧ Cst b ∧
      Fr a b [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex]) := by
  unfold returnPreparedInput
  refine (Hs.seq (t2 := 5 * L + 4)
    (hs_copy C StageRecovery.tokenLengthVar preparedLength a (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let b := a.set StageRecovery.tokenLengthVar (a.env preparedLength)
  refine (StageRecovery.inputReturnProgram_spec C b L base hlen hip hfit).mono le_rfl ?_
  rintro d ⟨hdi, hdrest, hdfr⟩
  have hf : Fr a d [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex] :=
    (Fr.set a _ (by simp)).trans (hdfr.weaken (by simp))
  exact ⟨hdi, hdrest, (hf _ (by decide)).trans hlen, Cst.of_fr hc hf (by decide), hf⟩

/-- Step 3 and `lem:print`, paper/paper.tex: acquire the exact original preparation word once,
then return the original input for the existing source/index decoder. -/
def cachePreparedInput : St VV MM := .seq acquirePreparedCache returnPreparedInput

/-- Step 3 and `lem:print`, paper/paper.tex: caching has no Gamma-sized return pass. It ends at
the original source head, with a real finite raw prefix and measured
length in a disjoint store, and no decoded-source side input. -/
theorem cachePreparedInput_spec (C : Ctx) (c : Call) (p : Cells.Parameters)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = StageMain.Compact.compactInput c p witness ++ rest)
    (hW : (preparedPrefixWord c p).length + 2 ≤ C.Wd)
    (hcap : (StageMain.Compact.compactInput c p witness).length < 2 ^ C.Wd)
    (hempty : a.ram preparedStore = [] ∧ a.rc preparedStore = 0) :
    Hs C cachePreparedInput a
      (StageMain.Compact.acquireCost c p witness +
        5 * (StageMain.Compact.compactInput c p witness).length + 9) (fun b =>
      b.ip = a.ip ∧ b.env preparedLength = (StageMain.Compact.compactInput c p witness).length ∧
      b.ram preparedStore = (StageMain.Compact.compactInput c p witness).map Bool.toNat ∧
      b.rc preparedStore = (StageMain.Compact.compactInput c p witness).length ∧
      (∀ store, store ≠ preparedStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (preparedLength :: StageRecovery.tokenLengthVar ::
        StageRecovery.inputReturnIndex :: StageMain.Compact.acquireScratch)) := by
  unfold cachePreparedInput
  refine (Hs.seq (t1 := StageMain.Compact.acquireCost c p witness + 2)
    (t2 := 5 * (StageMain.Compact.compactInput c p witness).length + 6)
    (acquirePreparedCache_spec C c p witness rest a hc hin hW hcap hempty)
    fun b ⟨hbi, hbl, hbram, hbrc, hbo, hbsh, hbc, hbfr⟩ => ?_).mono
      (by omega) (fun _ h => h)
  refine (returnPreparedInput_spec C b hbc _ a.ip hbl hbi hcap).mono le_rfl ?_
  rintro d ⟨hdi, hdrest, hdl, hdc, hdfr⟩
  have hdram : d.ram = b.ram := congrArg (fun t => t.2.1) hdrest
  have hdrc : d.rc = b.rc := congrArg (fun t => t.2.2.1) hdrest
  have hdsh : (d.out, d.kin, d.kout, d.kc) = (b.out, b.kin, b.kout, b.kc) :=
    congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdrest
  refine ⟨hdi, hdl, by rw [hdram]; exact hbram, by rw [hdrc]; exact hbrc,
    ?_, hdsh.trans hbsh, hdc, ?_⟩
  · intro store hs
    rw [hdram, hdrc]
    exact hbo store hs
  · exact (hbfr.weaken (by
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      tauto)).trans (hdfr.weaken (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto))

end NearQuarticWires.StageLift
