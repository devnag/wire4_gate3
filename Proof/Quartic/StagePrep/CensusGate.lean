import Proof.Quartic.StagePrep.CensusWeights

/-!
# Counting one physical threshold occurrence

Paper: `def:class`, paper/paper.tex; preparation in
`prop:time`. The threshold contributes no input
wire and the occurrence contributes one top wire.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicWires.RepairRepresentation (natWord)

/-- The gate census of `def:class`, paper/paper.tex. -/
def countGate : St VV :=
  .seq readNat (.seq (.op (.copy weightLength t3))
    (.seq (.op (.zero weightIndex)) (.seq countWeights
      (.seq readInt (.op (.inc censusTotal))))))

/-- Registers changed while counting one occurrence in
`def:class`, paper/paper.tex. -/
def gateCensusT : List (Fin VV) :=
  [censusTotal, weightIndex, weightLength, t0, t1, t2, t3, t4, t8, vJ, vPOS]

/-- One actual occurrence of `def:class`, paper/paper.tex, adds its fan-in plus one, irrespective of its threshold. -/
theorem countGate_spec (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (rest : List Bool) (a : DS VV) (hc : Cst a)
    (hcw : C.cw.drop a.cp = gateWord g ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + n + 2 < 2 ^ C.Wd) :
    Hs C countGate a (120 * (C.cw.length + 2) ^ 2) (fun b =>
      b.env censusTotal = a.env censusTotal + (Transfer.fanIn g + 1) ∧
      b.cp = a.cp + (gateWord g).length ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b gateCensusT) := by
  let ws := List.ofFn g.weight
  have hws : ws.length = n := by simp [ws]
  have hg : gateWord g = natWord ws.length ++
      (ws.flatMap intWord ++ intWord g.threshold) := by
    simp [gateWord, listWord, ws, List.append_assoc]
  have hlen := len_le_of_drop hcw
  have hnlen : n ≤ C.cw.length := by
    have hwlen := length_le_flatMap ws intWord intWord_len_pos
    rw [hg] at hlen
    simp only [List.length_append] at hlen
    omega
  have hnbit : natBitLength ws.length ≤ C.cw.length := by
    have hnb := natBitLength_le_len ws.length
    rw [hg] at hlen
    simp only [List.length_append] at hlen
    omega
  have hthreshold : (intWord g.threshold).length ≤ C.cw.length := by
    rw [hg] at hlen
    simp only [List.length_append] at hlen
    omega
  rw [hg, List.append_assoc] at hcw
  unfold countGate
  refine Hx.hs (Hs.then (readNat_spec a hc ws.length _ hcw (by omega) hL)
    (fun b ⟨hb3, _, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  refine Hs.then (hs_copy C weightLength t3 b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  refine Hs.then (hs_zero C weightIndex _) (fun e he n3 hn3 => ?_)
  subst he
  let d := (b.set weightLength (b.env t3)).set weightIndex 0
  have hdc : Cst d := by
    refine Cst.of_fr (T := [weightLength, weightIndex]) hbc
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))) (by decide) ?_
    simp only [d, DS.set_cp]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]
    exact hbc.pos
  have hdcw : C.cw.drop d.cp = ws.flatMap intWord ++ intWord g.threshold ++ rest := by
    change C.cw.drop b.cp = _
    rw [hbcp, ← List.drop_drop, hcw, List.drop_left, List.append_assoc]
  have hdt : d.env censusTotal = a.env censusTotal := by
    simp only [d]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hbfr _ (by decide)]
  refine Hs.then (countWeights_spec C ws (intWord g.threshold ++ rest) d hdc
    (by simp [d]) (by simp only [d]; rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hb3])
    (by simpa only [List.append_assoc] using hdcw) hW hL (by rw [hdt, hws]; omega))
    (fun f ⟨hft, hfcp, hfwq, hfout, hfc, hffr, _, _⟩ n4 hn4 => ?_)
  have hfcw : C.cw.drop f.cp = intWord g.threshold ++ rest := by
    rw [hfcp, ← List.drop_drop]
    rw [show C.cw.drop d.cp = ws.flatMap intWord ++ (intWord g.threshold ++ rest) by
      simpa only [List.append_assoc] using hdcw]
    rw [List.drop_left]
  refine Hs.then (readInt_spec f hfc g.threshold rest hfcw hW hL)
    (fun q ⟨_, _, _, hqcp, hqwq, hqout, hqc, hqfr⟩ n5 hn5 => ?_)
  have hqt : q.env censusTotal = a.env censusTotal + wireSum ws := by
    rw [hqfr _ (by decide), hft, hdt]
  have hsum : wireSum ws ≤ n := by simpa only [hws] using wireSum_le_length ws
  refine Hs.last (hs_inc C censusTotal q (by rw [hqt]; omega)) ?_
  rintro z rfl n6 hn6
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [DS.set_env_self, hqt, fanIn_eq_wireSum]
    rfl
  · rw [DS.set_cp, hqcp, hfcp]
    change b.cp + (ws.flatMap intWord).length + (intWord g.threshold).length = _
    rw [hbcp, hg]
    simp only [List.length_append]
    omega
  · rw [DS.set_wq, hqwq, hfwq]
    exact hbwq
  · rw [DS.set_out, hqout, hfout]
    exact hbout
  · exact Cst.of_fr (T := [censusTotal]) hqc (Fr.set _ _ (by decide))
      (by decide) (by rw [DS.set_env_ne _ _ (by decide)]; exact hqc.pos)
  · exact Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.weaken hffr (by decide)) (Fr.trans (Fr.weaken hqfr (by decide))
        (Fr.set _ _ (by decide))))))
  · have hprod := Nat.mul_le_mul_right (60 * C.cw.length + 77) hnlen
    rw [hws] at hn4
    nlinarith only [hn1, hn2, hn3, hn4, hn5, hn6, hprod, hnbit, hthreshold]

end NearQuarticWires.StagePrep
