import Proof.Quartic.StageMainMask.ReplyFrameRead

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: retain an actual framed witness or Gamma-table word
once, ending immediately after its terminal marker. -/
def readReplyFrame (store : Fin MM) : St VV MM :=
  .seq (.op (.rdK t0)) (.loop (.eq t0 v1) (replyReadBody store))

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the framed payload loop is linear in the number of
stored bits, with every marker and record write charged. -/
theorem replyFrameLoop_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0 = (frameFlag bits).toNat)
    (hin : a.kout.drop a.kc = framePayload bits ++ rest)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (.loop (.eq t0 v1) (replyReadBody store)) a (8 * bits.length + 2) (fun b =>
      b.env t0 = 0 ∧ b.kc = a.kc + 2 * bits.length ∧
      b.ram store = a.ram store ++ bits.map Bool.toNat ∧
      b.rc store = a.rc store + bits.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.ip, b.out, b.kin, b.kout) = (a.ip, a.out, a.kin, a.kout) ∧
      Cst b ∧ Fr a b [t0, t1]) := by
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp, ?_⟩
      exact ⟨by simpa [frameFlag] using hflag, by simp, by simp, by simp,
        fun _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      have hinput : a.kout.drop a.kc = bit :: frameFlag bits :: (framePayload bits ++ rest) := by
        change a.kout.drop a.kc = (bit :: frame bits) ++ rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      obtain ⟨b, n, hb, hn, hbeq⟩ := replyReadBody_spec C store a bit (frameFlag bits)
        (framePayload bits ++ rest) hinput hcursor
      subst b
      have hbc : Cst (replyReadStep a store bit (frameFlag bits)) := by
        constructor
        · simpa (config := {decide := true}) [replyReadStep] using hc.z
        · simpa (config := {decide := true}) [replyReadStep] using hc.one
        · simpa (config := {decide := true}) [replyReadStep] using hc.two
      have hbf : Fr a (replyReadStep a store bit (frameFlag bits)) [t0, t1] := by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [replyReadStep, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
      have hbin : (replyReadStep a store bit (frameFlag bits)).kout.drop (replyReadStep a store bit (frameFlag bits)).kc =
          framePayload bits ++ rest := by
        change a.kout.drop (a.kc + 2) = _
        rw [← List.drop_drop, hinput]
        rfl
      have hbcur : (replyReadStep a store bit (frameFlag bits)).rc store =
          ((replyReadStep a store bit (frameFlag bits)).ram store).length := by
        simp only [replyReadStep, Function.update_self, List.length_append, List.length_singleton]
        rw [hcursor]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdr, hdrc, hdother, hdsh, hdc, hdf⟩ :=
        ih (replyReadStep a store bit (frameFlag bits)) hbc
          (by simp [replyReadStep]) hbin hbcur
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd, by simp; omega, ?_⟩
      refine ⟨hdz, ?_, ?_, ?_, ?_, hdsh, hdc, hbf.trans hdf⟩
      · rw [hdi]
        change a.kc + 2 + 2 * bits.length = a.kc + 2 * (bit :: bits).length
        simp only [List.length_cons]
        omega
      · rw [hdr]
        simp [replyReadStep, List.map_cons, List.append_assoc]
      · rw [hdrc]
        simp only [replyReadStep, Function.update_self, List.length_cons]
        omega
      · intro other hother
        simpa only [replyReadStep, Function.update_of_ne hother] using hdother other hother

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the cold framed-word parser consumes the exact original
frame and preserves its following arbitrary source suffix. -/
theorem readReplyFrame_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : a.kout.drop a.kc = frame bits ++ rest)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (readReplyFrame store) a (8 * bits.length + 4) (fun b =>
      b.kc = a.kc + (frame bits).length ∧
      b.ram store = a.ram store ++ bits.map Bool.toNat ∧
      b.rc store = a.rc store + bits.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.ip, b.out, b.kin, b.kout) = (a.ip, a.out, a.kin, a.kout) ∧
      Cst b ∧ Fr a b [t0, t1]) := by
  unfold readReplyFrame
  refine (Hs.seq (t2 := 8 * bits.length + 2)
    (readReplySourceBit_spec C t0 a (frameFlag bits) (framePayload bits ++ rest)
      (by simpa only [frame_decompose, List.cons_append] using hin)) fun b hb => ?_).mono
      (by omega) (fun _ h => h)
  subst b
  have hbc : Cst ({ a.set t0 (frameFlag bits).toNat with kc := a.kc + 1 } : DS VV MM) := by
    constructor
    · simpa (config := {decide := true}) [DS.set] using hc.z
    · simpa (config := {decide := true}) [DS.set] using hc.one
    · simpa (config := {decide := true}) [DS.set] using hc.two
  have hinput : a.kout.drop (a.kc + 1) = framePayload bits ++ rest := by
    rw [← List.drop_drop, hin, frame_decompose]
    rfl
  refine (replyFrameLoop_spec C store bits rest _ hbc (by simp) hinput hcursor).mono le_rfl ?_
  rintro b ⟨_hbz, hbi, hbr, hbrc, hbother, hbsh, hbc', hbf⟩
  refine ⟨?_, hbr, hbrc, hbother, hbsh, hbc', ?_⟩
  · simp only [frame_length] at *
    change b.kc = a.kc + 1 + 2 * bits.length at hbi
    omega
  · exact Fr.trans (Fr.set a _ (by simp)) hbf

end NearQuarticWires.StageMainMask
