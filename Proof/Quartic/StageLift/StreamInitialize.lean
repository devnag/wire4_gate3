import Proof.Quartic.StageLift.StreamPayload

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: the retained
marker records are exactly the header bits, including the physical zero
sentinel that terminates payload replay. -/
theorem marker_prefix_eq (n : ℕ) :
    List.replicate n (1 : ℕ) ++ [0] =
      (unaryFlag n :: unaryTail n).map Bool.toNat := by
  rw [unaryWord_eq]
  simp

/-- `lem:print`, paper/paper.tex: replay starts
with accumulator zero, place value one and the first actual marker read. -/
def initializeStreamPayload (store : Fin MM) : St VV MM :=
  .seq (.op (.rwM store)) (.seq (.op (.zero leftVar))
    (.seq (.op (.copy streamPowerVar v1)) (.op (.rdM store t0))))

/-- `lem:print`, paper/paper.tex: initialization
physically rewinds the marker store and reads an in-range first marker.
It preserves every retained source and leaves an exact marker suffix. -/
theorem initializeStreamPayload_spec (C : Ctx) (store : Fin MM) (n : ℕ)
    (original : List ℕ) (a : DS VV MM) (hc : Cst a)
    (ha : a.ram store = wr original 0 (List.replicate n 1 ++ [0])) :
    Hs C (initializeStreamPayload store) a (a.rc store + 7) (fun b =>
      b.env leftVar = 0 ∧ b.env streamPowerVar = 1 ∧
      b.env t0 = (unaryFlag n).toNat ∧ b.ip = a.ip ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store 1 ∧
      (b.ram store).drop (b.rc store) = (unaryTail n).map Bool.toNat ++ original.drop (n + 1) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b payloadBodyScratch) := by
  have hlen : 0 < (a.ram store).length := by
    have hl := wr_length original (List.replicate n 1 ++ [0])
    rw [← ha] at hl
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hl
    omega
  have hfirst : (a.ram store).getD 0 0 = (unaryFlag n).toNat := by
    rw [ha, getD_wr original (List.replicate n 1 ++ [0]) 0 (by simp)]
    cases n <;> simp [unaryFlag, List.replicate_succ]
  unfold initializeStreamPayload
  refine Hs.seq (t1 := a.rc store + 1) (t2 := 5) (hs_rwM C store a) fun b hb => ?_
  subst b
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_zero C leftVar _) fun b hb => ?_
  subst b
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C streamPowerVar v1 _ (by decide)) fun b hb => ?_
  subst b
  let b := ((a.rew store).set leftVar 0).set streamPowerVar
    (((a.rew store).set leftVar 0).env v1)
  have hbone : b.env streamPowerVar = 1 := by
    simp (config := {decide := true}) [b, DS.rew, DS.set, hc.one]
  refine (hs_rdM C store t0 b (by simpa only [b, DS.rew, DS.set, Function.update_self] using hlen)).mono
    le_rfl ?_
  rintro d rfl
  have hf : Fr a ((b.set t0 ((b.ram store).getD (b.rc store) 0)).adv store) payloadBodyScratch :=
    (Fr.set (T := payloadBodyScratch) a 0 (by simp [payloadBodyScratch])).trans
      ((Fr.set _ _ (by simp [payloadBodyScratch])).trans (Fr.set _ _ (by simp [payloadBodyScratch])))
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_, ?_, rfl, Cst.of_fr hc hf (by decide), hf⟩
  · simp (config := {decide := true}) [b, DS.adv, DS.set]
  · simpa (config := {decide := true}) [DS.adv, DS.set] using hbone
  · simp only [DS.adv, DS.set_env_self]
    simpa only [b, DS.rew, DS.set, Function.update_self] using hfirst
  · simp only [b, DS.adv, DS.set, DS.rew, Function.update_self, Nat.zero_add, Function.update_idem]
  · simp only [b, DS.adv, DS.set, DS.rew, Function.update_self, Nat.zero_add, ha, wr,
      List.take_zero, List.nil_append, List.length_append, List.length_replicate,
      List.length_singleton]
    rw [marker_prefix_eq]
    simp only [List.map_cons, List.cons_append, List.drop_succ_cons, List.drop_zero]

end NearQuarticWires.StageLift
