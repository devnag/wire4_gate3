import Proof.Quartic.StageMainMask.CallData
import Proof.Quartic.StageMainMask.PopulationReply

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageMain StageLift

private def replyStoreOpDecision {V M : ℕ} (store : Fin M) (op : Op V M) :
    Decidable (avoidsStoreOp store op) := by
  cases op <;> dsimp only [avoidsStoreOp] <;> infer_instance

private def replyStoreDecision {V M : ℕ} (store : Fin M) :
    (s : St V M) → Decidable (avoidsStore store s)
  | .op op => replyStoreOpDecision store op
  | .seq s t => @instDecidableAnd _ _ (replyStoreDecision store s) (replyStoreDecision store t)
  | .ite _ s t => @instDecidableAnd _ _ (replyStoreDecision store s) (replyStoreDecision store t)
  | .loop _ s => replyStoreDecision store s

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
source acquisition, actual four-corner production and measured source
length loading precede every numeric-entry subroutine invocation. -/
def entryReadyCore : St VV MM := .seq entryPointCore makeEntryCallReady

/-- `prop:time`, paper/paper.tex: the source and
point production leaves the separate population-reply store untouched. -/
theorem entryReadyCore_avoids_reply : avoidsStore populationReplyStore entryReadyCore := by
  letI := replyStoreDecision populationReplyStore entryReadyCore
  decide

/-- Step 4 of `sec:algorithm`, `def:mask` and `prop:time`,
paper/paper.tex:
the literal original entry word supplies all retained sources, their
runtime copy lengths and the four actual corners; the reply store is
still empty and every source cursor is physically valid. -/
theorem entryReadyCore_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = entryWord r ++ rest)
    (hwidth : (entryWord r).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd)
    (hnwidth : r.call.n + 4 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C entryReadyCore a (entryPointCoreSteps r + 121) (fun b =>
      EntryNumericData r b ∧ b.ip = a.ip + (entryWord r).length ∧ b.out = a.out ∧
      Cst b ∧ (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc) ∧
      (∀ store, b.rc store ≤ (b.ram store).length) ∧
      b.ram populationReplyStore = [] ∧ b.rc populationReplyStore = 0) := by
  obtain ⟨b, n1, he1, hn1, hb, hbip, hbo, hbc, hbstreams⟩ :=
    entryPointCore_run C r rest a hc hin hwidth h64 hnwidth hempty
  obtain ⟨d, n2, he2, hn2, hd, hdip, hdo, hdc, hdstreams⟩ :=
    makeEntryCallReady_run C r b hbc hb (lt_trans (by omega) Nat.lt_two_pow_self)
  have he := Ex.seq he1 he2
  have hem := avoidsStore_spec he entryReadyCore_avoids_reply
  refine ⟨d, n1 + n2 + 1, he, by omega, hd.source, hdip.trans hbip, hdo.trans hbo,
    hdc, hdstreams.trans hbstreams, ?_, hem.1.trans (hempty _).1, hem.2.trans (hempty _).2⟩
  exact he.rc_le (by intro store; rw [(hempty store).1, (hempty store).2]; exact Nat.zero_le _)

end NearQuarticWires.StageMainMask
