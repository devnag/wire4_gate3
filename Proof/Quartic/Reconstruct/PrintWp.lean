import Proof.Quartic.Reconstruct.PrintScanParamsRun

/-!
# The length of the word after parameter preparation

Paper: `sec:params`, paper/paper.tex (the witness prefix has `k + (J+1)(G_1+G_2)` bits), and Step 3 of
`sec:algorithm`.

After the call and the parameters have been read and counted (`c` bits), `wpLenS` computes `2mG_j = (ω_j - 1)/2`
(`ω_j = 4mG_j + 1`, `m = 4`) into `kB0`, `kB1`, the number `c + 2(k + (J+1)(G_1 + G_2)) + 1` of bits of `prepWord`
into `kPL`, and `c` into `kR` (`wpLenS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx}

/-- The number of bits to rewind. -/
def kR : Fin VV := ⟨96, by decide⟩
/-- The number of bits of `prepWord`. -/
def kPL : Fin VV := ⟨97, by decide⟩
/-- A temporary. -/
def kT1 : Fin VV := ⟨98, by decide⟩

/-- The variables written by `wpLenS`. -/
def wpLenT : List (Fin VV) := [kB0, kB1, kT1, kPL, kR]

/-- `2mG_1`, `2mG_2` from `ω_1`, `ω_2`. -/
def wpA : St VV MM := (.seq (.op (.copy kB0 kO1)) (.seq (.op (.sub kB0 v1)) (.seq (.op (.half kB0)) (.seq (.op (.copy kB1 kO2)) (.seq (.op (.sub kB1 v1)) (.op (.half kB1)))))))
/-- `G_1 + G_2` from `2mG_1`, `2mG_2`. -/
def wpB : St VV MM := (.seq (.op (.copy kT1 kB0)) (.seq (.op (.half kT1)) (.seq (.op (.half kT1)) (.seq (.op (.half kT1)) (.seq (.op (.copy kPL kB1)) (.seq (.op (.half kPL)) (.seq (.op (.half kPL)) (.seq (.op (.half kPL)) (.op (.add kPL kT1))))))))))
/-- `|prepWord|` and the rewind count. -/
def wpC : St VV MM := (.seq (.op (.copy kT1 kJ1)) (.seq (.op (.inc kT1)) (.seq (.op (.mul kT1 kPL kR)) (.seq (.op (.add kR kK)) (.seq (.op (.copy kPL kR)) (.seq (.op (.add kPL kR)) (.seq (.op (.inc kPL)) (.seq (.op (.add kPL lengthCounter)) (.op (.copy kR lengthCounter))))))))))

/-- `2mG_j`, `|prepWord|` and the rewind count from `ω_1`, `ω_2`, `J`, `k` and the count. -/
def wpLenS : St VV MM := .seq wpA (.seq wpB wpC)

theorem wpA_spec (a : DS VV MM) (hc : Cst a) (o1 o2 : ℕ) (h1 : a.env kO1 = o1) (h2 : a.env kO2 = o2) (ho1 : 1 ≤ o1)
    (ho2 : 1 ≤ o2) :
    Hs C wpA a 11 (fun b => b.env kB0 = (o1 - 1) / 2 ∧ b.env kB1 = (o2 - 1) / 2 ∧ Same a b ∧ Fr a b wpLenT ∧ Cst b) := by
  unfold wpA
  refine Hx.hs (Hs.then (hs_copy C kB0 kO1 a (by decide)) (fun s1 e1 n1 hn1 => ?_))
  have f1_kB0 : s1.env kB0 = o1 := by rw [e1, DS.set_env_self, h1]
  have f1_kO1 : s1.env kO1 = o1 := by rw [e1, DS.set_env_ne _ _ (by decide), h1]
  have f1_kO2 : s1.env kO2 = o2 := by rw [e1, DS.set_env_ne _ _ (by decide), h2]
  have f1_v1 : s1.env v1 = 1 := by rw [e1, DS.set_env_ne _ _ (by decide), hc.one]
  have sm1 : Same a s1 := by rw [e1]; exact Same.set _ _ _
  have fr1 : Fr a s1 wpLenT := by rw [e1]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_sub C kB0 v1 s1 (by decide) (by rw [f1_v1, f1_kB0]; omega)) (fun s2 e2 n2 hn2 => ?_)
  have f2_kB0 : s2.env kB0 = (o1 - 1) := by rw [e2, DS.set_env_self, f1_kB0, f1_v1]
  have f2_kO1 : s2.env kO1 = o1 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kO1]
  have f2_kO2 : s2.env kO2 = o2 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kO2]
  have f2_v1 : s2.env v1 = 1 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_v1]
  have sm2 : Same s1 s2 := by rw [e2]; exact Same.set _ _ _
  have fr2 : Fr s1 s2 wpLenT := by rw [e2]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kB0 s2) (fun s3 e3 n3 hn3 => ?_)
  have f3_kB0 : s3.env kB0 = ((o1 - 1) / 2) := by rw [e3, DS.set_env_self, f2_kB0]
  have f3_kO1 : s3.env kO1 = o1 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kO1]
  have f3_kO2 : s3.env kO2 = o2 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kO2]
  have f3_v1 : s3.env v1 = 1 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_v1]
  have sm3 : Same s2 s3 := by rw [e3]; exact Same.set _ _ _
  have fr3 : Fr s2 s3 wpLenT := by rw [e3]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C kB1 kO2 s3 (by decide)) (fun s4 e4 n4 hn4 => ?_)
  have f4_kB1 : s4.env kB1 = o2 := by rw [e4, DS.set_env_self, f3_kO2]
  have f4_kB0 : s4.env kB0 = ((o1 - 1) / 2) := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kB0]
  have f4_kO1 : s4.env kO1 = o1 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kO1]
  have f4_kO2 : s4.env kO2 = o2 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kO2]
  have f4_v1 : s4.env v1 = 1 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_v1]
  have sm4 : Same s3 s4 := by rw [e4]; exact Same.set _ _ _
  have fr4 : Fr s3 s4 wpLenT := by rw [e4]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_sub C kB1 v1 s4 (by decide) (by rw [f4_v1, f4_kB1]; omega)) (fun s5 e5 n5 hn5 => ?_)
  have f5_kB1 : s5.env kB1 = (o2 - 1) := by rw [e5, DS.set_env_self, f4_kB1, f4_v1]
  have f5_kB0 : s5.env kB0 = ((o1 - 1) / 2) := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kB0]
  have f5_kO1 : s5.env kO1 = o1 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kO1]
  have f5_kO2 : s5.env kO2 = o2 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kO2]
  have f5_v1 : s5.env v1 = 1 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_v1]
  have sm5 : Same s4 s5 := by rw [e5]; exact Same.set _ _ _
  have fr5 : Fr s4 s5 wpLenT := by rw [e5]; exact Fr.set _ _ (by decide)
  refine Hs.last (hs_half C kB1 s5) (fun s6 e6 n6 hn6 => ?_)
  have f6_kB1 : s6.env kB1 = ((o2 - 1) / 2) := by rw [e6, DS.set_env_self, f5_kB1]
  have f6_kB0 : s6.env kB0 = ((o1 - 1) / 2) := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kB0]
  have f6_kO1 : s6.env kO1 = o1 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kO1]
  have f6_kO2 : s6.env kO2 = o2 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kO2]
  have f6_v1 : s6.env v1 = 1 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_v1]
  have sm6 : Same s5 s6 := by rw [e6]; exact Same.set _ _ _
  have fr6 : Fr s5 s6 wpLenT := by rw [e6]; exact Fr.set _ _ (by decide)
  have smA : Same a s6 := (((((sm1.trans sm2).trans sm3).trans sm4).trans sm5).trans sm6)
  have frA : Fr a s6 wpLenT := (((((fr1.trans fr2).trans fr3).trans fr4).trans fr5).trans fr6)
  exact ⟨⟨f6_kB0, f6_kB1, smA, frA, Cst.of_fr hc frA (by decide)⟩, by linarith only [hn1, hn2, hn3, hn4, hn5, hn6]⟩

theorem wpB_spec (a : DS VV MM) (B0 B1 : ℕ) (h1 : a.env kB0 = B0) (h2 : a.env kB1 = B1)
    (hbig : B0 / 2 / 2 / 2 + B1 / 2 / 2 / 2 < 2 ^ C.Wd) :
    Hs C wpB a 17 (fun b => b.env kPL = B1 / 2 / 2 / 2 + B0 / 2 / 2 / 2 ∧ b.env kB0 = B0 ∧ b.env kB1 = B1 ∧
      Same a b ∧ Fr a b wpLenT) := by
  unfold wpB
  refine Hx.hs (Hs.then (hs_copy C kT1 kB0 a (by decide)) (fun s1 e1 n1 hn1 => ?_))
  have f1_kT1 : s1.env kT1 = B0 := by rw [e1, DS.set_env_self, h1]
  have f1_kB0 : s1.env kB0 = B0 := by rw [e1, DS.set_env_ne _ _ (by decide), h1]
  have f1_kB1 : s1.env kB1 = B1 := by rw [e1, DS.set_env_ne _ _ (by decide), h2]
  have sm1 : Same a s1 := by rw [e1]; exact Same.set _ _ _
  have fr1 : Fr a s1 wpLenT := by rw [e1]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kT1 s1) (fun s2 e2 n2 hn2 => ?_)
  have f2_kT1 : s2.env kT1 = (B0 / 2) := by rw [e2, DS.set_env_self, f1_kT1]
  have f2_kB0 : s2.env kB0 = B0 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kB0]
  have f2_kB1 : s2.env kB1 = B1 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kB1]
  have sm2 : Same s1 s2 := by rw [e2]; exact Same.set _ _ _
  have fr2 : Fr s1 s2 wpLenT := by rw [e2]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kT1 s2) (fun s3 e3 n3 hn3 => ?_)
  have f3_kT1 : s3.env kT1 = ((B0 / 2) / 2) := by rw [e3, DS.set_env_self, f2_kT1]
  have f3_kB0 : s3.env kB0 = B0 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kB0]
  have f3_kB1 : s3.env kB1 = B1 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kB1]
  have sm3 : Same s2 s3 := by rw [e3]; exact Same.set _ _ _
  have fr3 : Fr s2 s3 wpLenT := by rw [e3]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kT1 s3) (fun s4 e4 n4 hn4 => ?_)
  have f4_kT1 : s4.env kT1 = (((B0 / 2) / 2) / 2) := by rw [e4, DS.set_env_self, f3_kT1]
  have f4_kB0 : s4.env kB0 = B0 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kB0]
  have f4_kB1 : s4.env kB1 = B1 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kB1]
  have sm4 : Same s3 s4 := by rw [e4]; exact Same.set _ _ _
  have fr4 : Fr s3 s4 wpLenT := by rw [e4]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C kPL kB1 s4 (by decide)) (fun s5 e5 n5 hn5 => ?_)
  have f5_kPL : s5.env kPL = B1 := by rw [e5, DS.set_env_self, f4_kB1]
  have f5_kB0 : s5.env kB0 = B0 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kB0]
  have f5_kB1 : s5.env kB1 = B1 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kB1]
  have f5_kT1 : s5.env kT1 = (((B0 / 2) / 2) / 2) := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kT1]
  have sm5 : Same s4 s5 := by rw [e5]; exact Same.set _ _ _
  have fr5 : Fr s4 s5 wpLenT := by rw [e5]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kPL s5) (fun s6 e6 n6 hn6 => ?_)
  have f6_kPL : s6.env kPL = (B1 / 2) := by rw [e6, DS.set_env_self, f5_kPL]
  have f6_kB0 : s6.env kB0 = B0 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kB0]
  have f6_kB1 : s6.env kB1 = B1 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kB1]
  have f6_kT1 : s6.env kT1 = (((B0 / 2) / 2) / 2) := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kT1]
  have sm6 : Same s5 s6 := by rw [e6]; exact Same.set _ _ _
  have fr6 : Fr s5 s6 wpLenT := by rw [e6]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kPL s6) (fun s7 e7 n7 hn7 => ?_)
  have f7_kPL : s7.env kPL = ((B1 / 2) / 2) := by rw [e7, DS.set_env_self, f6_kPL]
  have f7_kB0 : s7.env kB0 = B0 := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kB0]
  have f7_kB1 : s7.env kB1 = B1 := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kB1]
  have f7_kT1 : s7.env kT1 = (((B0 / 2) / 2) / 2) := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kT1]
  have sm7 : Same s6 s7 := by rw [e7]; exact Same.set _ _ _
  have fr7 : Fr s6 s7 wpLenT := by rw [e7]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_half C kPL s7) (fun s8 e8 n8 hn8 => ?_)
  have f8_kPL : s8.env kPL = (((B1 / 2) / 2) / 2) := by rw [e8, DS.set_env_self, f7_kPL]
  have f8_kB0 : s8.env kB0 = B0 := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kB0]
  have f8_kB1 : s8.env kB1 = B1 := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kB1]
  have f8_kT1 : s8.env kT1 = (((B0 / 2) / 2) / 2) := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kT1]
  have sm8 : Same s7 s8 := by rw [e8]; exact Same.set _ _ _
  have fr8 : Fr s7 s8 wpLenT := by rw [e8]; exact Fr.set _ _ (by decide)
  refine Hs.last (hs_add C kPL kT1 s8 (by decide) (by rw [f8_kPL, f8_kT1]; omega)) (fun s9 e9 n9 hn9 => ?_)
  have f9_kPL : s9.env kPL = ((((B1 / 2) / 2) / 2) + (((B0 / 2) / 2) / 2)) := by rw [e9, DS.set_env_self, f8_kPL, f8_kT1]
  have f9_kB0 : s9.env kB0 = B0 := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kB0]
  have f9_kB1 : s9.env kB1 = B1 := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kB1]
  have f9_kT1 : s9.env kT1 = (((B0 / 2) / 2) / 2) := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kT1]
  have sm9 : Same s8 s9 := by rw [e9]; exact Same.set _ _ _
  have fr9 : Fr s8 s9 wpLenT := by rw [e9]; exact Fr.set _ _ (by decide)
  have smA : Same a s9 := ((((((((sm1.trans sm2).trans sm3).trans sm4).trans sm5).trans sm6).trans sm7).trans sm8).trans sm9)
  have frA : Fr a s9 wpLenT := ((((((((fr1.trans fr2).trans fr3).trans fr4).trans fr5).trans fr6).trans fr7).trans fr8).trans fr9)
  exact ⟨⟨f9_kPL, f9_kB0, f9_kB1, smA, frA⟩, by linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9]⟩

theorem wpC_spec (a : DS VV MM) (g J k c B0 B1 : ℕ) (h1 : a.env kPL = g) (hJ : a.env kJ1 = J) (hk : a.env kK = k)
    (hlc : a.env lengthCounter = c) (hb0 : a.env kB0 = B0) (hb1 : a.env kB1 = B1) (hJW : J + 1 < 2 ^ C.Wd)
    (hbig : c + 2 * (k + (J + 1) * g) + 1 < 2 ^ C.Wd) :
    Hs C wpC a 17 (fun b => b.env kPL = c + 2 * (k + (J + 1) * g) + 1 ∧ b.env kR = c ∧ b.env kB0 = B0 ∧
      b.env kB1 = B1 ∧ Same a b ∧ Fr a b wpLenT) := by
  unfold wpC
  refine Hx.hs (Hs.then (hs_copy C kT1 kJ1 a (by decide)) (fun s1 e1 n1 hn1 => ?_))
  have f1_kT1 : s1.env kT1 = J := by rw [e1, DS.set_env_self, hJ]
  have f1_kB0 : s1.env kB0 = B0 := by rw [e1, DS.set_env_ne _ _ (by decide), hb0]
  have f1_kB1 : s1.env kB1 = B1 := by rw [e1, DS.set_env_ne _ _ (by decide), hb1]
  have f1_kPL : s1.env kPL = g := by rw [e1, DS.set_env_ne _ _ (by decide), h1]
  have f1_kJ1 : s1.env kJ1 = J := by rw [e1, DS.set_env_ne _ _ (by decide), hJ]
  have f1_kK : s1.env kK = k := by rw [e1, DS.set_env_ne _ _ (by decide), hk]
  have f1_lengthCounter : s1.env lengthCounter = c := by rw [e1, DS.set_env_ne _ _ (by decide), hlc]
  have sm1 : Same a s1 := by rw [e1]; exact Same.set _ _ _
  have fr1 : Fr a s1 wpLenT := by rw [e1]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_inc C kT1 s1 (by rw [f1_kT1]; omega)) (fun s2 e2 n2 hn2 => ?_)
  have f2_kT1 : s2.env kT1 = (J + 1) := by rw [e2, DS.set_env_self, f1_kT1]
  have f2_kB0 : s2.env kB0 = B0 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kB0]
  have f2_kB1 : s2.env kB1 = B1 := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kB1]
  have f2_kPL : s2.env kPL = g := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kPL]
  have f2_kJ1 : s2.env kJ1 = J := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kJ1]
  have f2_kK : s2.env kK = k := by rw [e2, DS.set_env_ne _ _ (by decide), f1_kK]
  have f2_lengthCounter : s2.env lengthCounter = c := by rw [e2, DS.set_env_ne _ _ (by decide), f1_lengthCounter]
  have sm2 : Same s1 s2 := by rw [e2]; exact Same.set _ _ _
  have fr2 : Fr s1 s2 wpLenT := by rw [e2]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_mul C kT1 kPL kR s2 (by decide) (by decide) (by decide) (by rw [f2_kT1, f2_kPL]; omega)) (fun s3 e3 n3 hn3 => ?_)
  have f3_kR : s3.env kR = ((J + 1) * g) := by rw [e3, DS.set_env_self, f2_kT1, f2_kPL]
  have f3_kB0 : s3.env kB0 = B0 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kB0]
  have f3_kB1 : s3.env kB1 = B1 := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kB1]
  have f3_kT1 : s3.env kT1 = (J + 1) := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kT1]
  have f3_kPL : s3.env kPL = g := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kPL]
  have f3_kJ1 : s3.env kJ1 = J := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kJ1]
  have f3_kK : s3.env kK = k := by rw [e3, DS.set_env_ne _ _ (by decide), f2_kK]
  have f3_lengthCounter : s3.env lengthCounter = c := by rw [e3, DS.set_env_ne _ _ (by decide), f2_lengthCounter]
  have sm3 : Same s2 s3 := by rw [e3]; exact Same.set _ _ _
  have fr3 : Fr s2 s3 wpLenT := by rw [e3]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_add C kR kK s3 (by decide) (by rw [f3_kR, f3_kK]; omega)) (fun s4 e4 n4 hn4 => ?_)
  have f4_kR : s4.env kR = (((J + 1) * g) + k) := by rw [e4, DS.set_env_self, f3_kR, f3_kK]
  have f4_kB0 : s4.env kB0 = B0 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kB0]
  have f4_kB1 : s4.env kB1 = B1 := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kB1]
  have f4_kT1 : s4.env kT1 = (J + 1) := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kT1]
  have f4_kPL : s4.env kPL = g := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kPL]
  have f4_kJ1 : s4.env kJ1 = J := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kJ1]
  have f4_kK : s4.env kK = k := by rw [e4, DS.set_env_ne _ _ (by decide), f3_kK]
  have f4_lengthCounter : s4.env lengthCounter = c := by rw [e4, DS.set_env_ne _ _ (by decide), f3_lengthCounter]
  have sm4 : Same s3 s4 := by rw [e4]; exact Same.set _ _ _
  have fr4 : Fr s3 s4 wpLenT := by rw [e4]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_copy C kPL kR s4 (by decide)) (fun s5 e5 n5 hn5 => ?_)
  have f5_kPL : s5.env kPL = (((J + 1) * g) + k) := by rw [e5, DS.set_env_self, f4_kR]
  have f5_kB0 : s5.env kB0 = B0 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kB0]
  have f5_kB1 : s5.env kB1 = B1 := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kB1]
  have f5_kT1 : s5.env kT1 = (J + 1) := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kT1]
  have f5_kR : s5.env kR = (((J + 1) * g) + k) := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kR]
  have f5_kJ1 : s5.env kJ1 = J := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kJ1]
  have f5_kK : s5.env kK = k := by rw [e5, DS.set_env_ne _ _ (by decide), f4_kK]
  have f5_lengthCounter : s5.env lengthCounter = c := by rw [e5, DS.set_env_ne _ _ (by decide), f4_lengthCounter]
  have sm5 : Same s4 s5 := by rw [e5]; exact Same.set _ _ _
  have fr5 : Fr s4 s5 wpLenT := by rw [e5]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_add C kPL kR s5 (by decide) (by rw [f5_kPL, f5_kR]; omega)) (fun s6 e6 n6 hn6 => ?_)
  have f6_kPL : s6.env kPL = ((((J + 1) * g) + k) + (((J + 1) * g) + k)) := by rw [e6, DS.set_env_self, f5_kPL, f5_kR]
  have f6_kB0 : s6.env kB0 = B0 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kB0]
  have f6_kB1 : s6.env kB1 = B1 := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kB1]
  have f6_kT1 : s6.env kT1 = (J + 1) := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kT1]
  have f6_kR : s6.env kR = (((J + 1) * g) + k) := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kR]
  have f6_kJ1 : s6.env kJ1 = J := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kJ1]
  have f6_kK : s6.env kK = k := by rw [e6, DS.set_env_ne _ _ (by decide), f5_kK]
  have f6_lengthCounter : s6.env lengthCounter = c := by rw [e6, DS.set_env_ne _ _ (by decide), f5_lengthCounter]
  have sm6 : Same s5 s6 := by rw [e6]; exact Same.set _ _ _
  have fr6 : Fr s5 s6 wpLenT := by rw [e6]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_inc C kPL s6 (by rw [f6_kPL]; omega)) (fun s7 e7 n7 hn7 => ?_)
  have f7_kPL : s7.env kPL = (((((J + 1) * g) + k) + (((J + 1) * g) + k)) + 1) := by rw [e7, DS.set_env_self, f6_kPL]
  have f7_kB0 : s7.env kB0 = B0 := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kB0]
  have f7_kB1 : s7.env kB1 = B1 := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kB1]
  have f7_kT1 : s7.env kT1 = (J + 1) := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kT1]
  have f7_kR : s7.env kR = (((J + 1) * g) + k) := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kR]
  have f7_kJ1 : s7.env kJ1 = J := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kJ1]
  have f7_kK : s7.env kK = k := by rw [e7, DS.set_env_ne _ _ (by decide), f6_kK]
  have f7_lengthCounter : s7.env lengthCounter = c := by rw [e7, DS.set_env_ne _ _ (by decide), f6_lengthCounter]
  have sm7 : Same s6 s7 := by rw [e7]; exact Same.set _ _ _
  have fr7 : Fr s6 s7 wpLenT := by rw [e7]; exact Fr.set _ _ (by decide)
  refine Hs.then (hs_add C kPL lengthCounter s7 (by decide) (by rw [f7_kPL, f7_lengthCounter]; omega)) (fun s8 e8 n8 hn8 => ?_)
  have f8_kPL : s8.env kPL = ((((((J + 1) * g) + k) + (((J + 1) * g) + k)) + 1) + c) := by rw [e8, DS.set_env_self, f7_kPL, f7_lengthCounter]
  have f8_kB0 : s8.env kB0 = B0 := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kB0]
  have f8_kB1 : s8.env kB1 = B1 := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kB1]
  have f8_kT1 : s8.env kT1 = (J + 1) := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kT1]
  have f8_kR : s8.env kR = (((J + 1) * g) + k) := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kR]
  have f8_kJ1 : s8.env kJ1 = J := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kJ1]
  have f8_kK : s8.env kK = k := by rw [e8, DS.set_env_ne _ _ (by decide), f7_kK]
  have f8_lengthCounter : s8.env lengthCounter = c := by rw [e8, DS.set_env_ne _ _ (by decide), f7_lengthCounter]
  have sm8 : Same s7 s8 := by rw [e8]; exact Same.set _ _ _
  have fr8 : Fr s7 s8 wpLenT := by rw [e8]; exact Fr.set _ _ (by decide)
  refine Hs.last (hs_copy C kR lengthCounter s8 (by decide)) (fun s9 e9 n9 hn9 => ?_)
  have f9_kR : s9.env kR = c := by rw [e9, DS.set_env_self, f8_lengthCounter]
  have f9_kB0 : s9.env kB0 = B0 := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kB0]
  have f9_kB1 : s9.env kB1 = B1 := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kB1]
  have f9_kT1 : s9.env kT1 = (J + 1) := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kT1]
  have f9_kPL : s9.env kPL = ((((((J + 1) * g) + k) + (((J + 1) * g) + k)) + 1) + c) := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kPL]
  have f9_kJ1 : s9.env kJ1 = J := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kJ1]
  have f9_kK : s9.env kK = k := by rw [e9, DS.set_env_ne _ _ (by decide), f8_kK]
  have f9_lengthCounter : s9.env lengthCounter = c := by rw [e9, DS.set_env_ne _ _ (by decide), f8_lengthCounter]
  have sm9 : Same s8 s9 := by rw [e9]; exact Same.set _ _ _
  have fr9 : Fr s8 s9 wpLenT := by rw [e9]; exact Fr.set _ _ (by decide)
  have smA : Same a s9 := ((((((((sm1.trans sm2).trans sm3).trans sm4).trans sm5).trans sm6).trans sm7).trans sm8).trans sm9)
  have frA : Fr a s9 wpLenT := ((((((((fr1.trans fr2).trans fr3).trans fr4).trans fr5).trans fr6).trans fr7).trans fr8).trans fr9)
  exact ⟨⟨by rw [f9_kPL]; ring, f9_kR, f9_kB0, f9_kB1, smA, frA⟩, by linarith only [hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9]⟩

/-- **The length of `prepWord`.** -/
theorem wpLenS_spec (a : DS VV MM) (hc : Cst a) (o1 o2 J k c : ℕ) (h1 : a.env kO1 = o1) (h2 : a.env kO2 = o2)
    (hJ : a.env kJ1 = J) (hk : a.env kK = k) (hlc : a.env lengthCounter = c) (ho1 : 1 ≤ o1) (ho2 : 1 ≤ o2)
    (hJW : J + 1 < 2 ^ C.Wd)
    (hbig : c + 2 * (k + (J + 1) * ((o1 - 1) / 2 / 2 / 2 / 2 + (o2 - 1) / 2 / 2 / 2 / 2)) + 1 < 2 ^ C.Wd) :
    Hs C wpLenS a 47 (fun b => b.env kB0 = (o1 - 1) / 2 ∧ b.env kB1 = (o2 - 1) / 2 ∧
      b.env kPL = c + 2 * (k + (J + 1) * ((o1 - 1) / 2 / 2 / 2 / 2 + (o2 - 1) / 2 / 2 / 2 / 2)) + 1 ∧
      b.env kR = c ∧ Same a b ∧ Fr a b wpLenT ∧ Cst b) := by
  have hle : (o1 - 1) / 2 / 2 / 2 / 2 + (o2 - 1) / 2 / 2 / 2 / 2 ≤
      (J + 1) * ((o1 - 1) / 2 / 2 / 2 / 2 + (o2 - 1) / 2 / 2 / 2 / 2) := Nat.le_mul_of_pos_left _ (by omega)
  refine Hx.hs (Hs.then (wpA_spec a hc o1 o2 h1 h2 ho1 ho2) (fun b1 ⟨x1, x2, sm1, fr1, c1⟩ n1 hn1 => ?_))
  refine Hs.then (wpB_spec b1 _ _ x1 x2 (by omega)) (fun b2 ⟨y1, y2, y3, sm2, fr2⟩ n2 hn2 => ?_)
  have k2 : ∀ y, y ∉ wpLenT → b2.env y = a.env y := fun y hy => (fr2 y hy).trans (fr1 y hy)
  have hcomm : (o2 - 1) / 2 / 2 / 2 / 2 + (o1 - 1) / 2 / 2 / 2 / 2 = (o1 - 1) / 2 / 2 / 2 / 2 + (o2 - 1) / 2 / 2 / 2 / 2 :=
    by omega
  refine Hs.last (wpC_spec b2 _ J k c _ _ y1 (by rw [k2 kJ1 (by decide), hJ]) (by rw [k2 kK (by decide), hk])
    (by rw [k2 lengthCounter (by decide), hlc]) y2 y3 hJW (by rw [hcomm]; exact hbig))
    (fun b3 ⟨z1, z2, z3, z4, sm3, fr3⟩ n3 hn3 => ⟨⟨z3, z4, by rw [z1, hcomm], z2, (sm1.trans sm2).trans sm3,
      (fr1.trans fr2).trans fr3, Cst.of_fr hc ((fr1.trans fr2).trans fr3) (by decide)⟩, by omega⟩)

end NearQuarticWires.Reconstruct
