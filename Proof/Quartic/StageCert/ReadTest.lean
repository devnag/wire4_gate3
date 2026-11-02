import Proof.Quartic.StageCert.StrictTest

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation

/-- `sec:algorithm`, paper/paper.tex: read a self-delimiting natural
field into a designated certificate register. -/
def readInto (x : Fin VV) : St VV MM := .seq rdNatI (.op (.copy x t3))

/-- `sec:algorithm`, paper/paper.tex: exact semantics and linear bit
cost of reading one certificate field. -/
theorem readInto_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (x : Fin VV) (hx : x ∉ rdNatT) (hcst : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2)
    (v : ℕ) (rest : List Bool) (hin : C.inp.drop a.ip = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (readInto x) a (30*natBitLength v+32) (fun b =>
      b.env x = v ∧ C.inp.drop b.ip = rest ∧ b.out = a.out ∧
      Cst b ∧ Fr a b (x :: rdNatT)) := by
  have hxt : x ≠ t3 := by intro he; subst he; exact hx (by simp [rdNatT])
  unfold readInto
  let Post : DS VV MM → Prop := fun b =>
    b.env x = v ∧ C.inp.drop b.ip = rest ∧ b.out = a.out ∧ Cst b ∧ Fr a b (x :: rdNatT)
  have hr : Hs C (.seq rdNatI (.op (.copy x t3))) a
      ((30*natBitLength v+30)+1+1) Post := by
    refine Hs.seq (t1 := 30*natBitLength v+30) (t2 := 1)
      (rdNatI_spec a hc v rest hin hW) (fun b hb => ?_)
    refine (hs_copy C x t3 b hxt).mono le_rfl ?_
    intro d hd
    subst d
    have hf : Fr a (b.set x (b.env t3)) (x :: rdNatT) := by
      intro y hy
      simp only [List.mem_cons, not_or] at hy
      rw [DS.set_env_ne _ _ hy.1]
      exact hb.2.2.2.2 y hy.2
    refine ⟨?_, ?_, ?_, ?_, hf⟩
    · simpa using hb.1
    · change C.inp.drop b.ip = rest
      rw [hb.2.2.1]
      exact drop_adv hin
    · exact congrArg Prod.fst hb.2.2.2.1
    · apply Cst.of_fr hc hf
      simp only [List.mem_cons, not_or]
      exact ⟨⟨Ne.symm hcst.1, by decide⟩,
        ⟨Ne.symm hcst.2.1, by decide⟩, ⟨Ne.symm hcst.2.2, by decide⟩⟩

  exact hr.mono (by omega) (fun _ h => h)

/-- `sec:algorithm`, paper/paper.tex: the three fields of a signed
moment test use the existing exact integer and natural codecs. -/
def readTest : St VV MM :=
  .seq (readInto testSign) (.seq (readInto testMagnitude) (readInto testBound))

end NearQuarticWires.StageCert

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: registers and
input cursor after reading one complete signed moment record. -/
structure TestLoaded (C : Ctx) (a b : DS VV MM) (z : ℤ) (R : ℕ) (rest : List Bool) : Prop where
  sign : b.env testSign = if z < 0 then 1 else 0
  magnitude : b.env testMagnitude = z.natAbs
  bound : b.env testBound = R
  tail : C.inp.drop b.ip = rest
  out : b.out = a.out
  cst : Cst b
  frame : Fr a b ([testSign, testMagnitude, testBound] ++ rdNatT)

/-- `sec:algorithm`, paper/paper.tex: exact physical signed-record
parser, with all signs, threshold bits and cursor movement retained. -/
theorem readTest_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ) (R : ℕ)
    (rest : List Bool)
    (hin : C.inp.drop a.ip = NearCubicGates.Close.Interfaces.intWord z ++ natWord R ++ rest)
    (hWs : natBitLength (if z < 0 then 1 else 0) + 2 ≤ C.Wd)
    (hWm : natBitLength z.natAbs + 2 ≤ C.Wd) (hWr : natBitLength R + 2 ≤ C.Wd) :
    Hs C readTest a
      (30*(natBitLength (if z < 0 then 1 else 0)+natBitLength z.natAbs+natBitLength R)+100)
      (fun b => TestLoaded C a b z R rest) := by
  have hs := readInto_run C a hc testSign (by decide)
    (by decide) (if z < 0 then 1 else 0) (natWord z.natAbs ++ natWord R ++ rest)
    (by simpa [NearCubicGates.Close.Interfaces.intWord, List.append_assoc] using hin) hWs
  let Post := fun b => TestLoaded C a b z R rest
  have hr : Hs C readTest a
      ((30*natBitLength (if z<0 then 1 else 0)+32)+
        ((30*natBitLength z.natAbs+32)+(30*natBitLength R+32)+1)+1) Post := by
    unfold readTest
    refine Hs.seq hs (fun b hb => ?_)
    refine Hs.seq (readInto_run C b hb.2.2.2.1 testMagnitude (by decide) (by decide)
      z.natAbs (natWord R ++ rest) (by simpa [List.append_assoc] using hb.2.1) hWm) (fun d hd => ?_)
    refine (readInto_run C d hd.2.2.2.1 testBound (by decide) (by decide)
      R rest hd.2.1 hWr).mono le_rfl ?_
    intro e he
    refine ⟨?_, ?_, he.1, he.2.1, he.2.2.1.trans (hd.2.2.1.trans hb.2.2.1), he.2.2.2.1, ?_⟩
    · rw [he.2.2.2.2 testSign (by decide), hd.2.2.2.2 testSign (by decide)]
      exact hb.1
    · rw [he.2.2.2.2 testMagnitude (by decide)]
      exact hd.1
    · exact Fr.trans (hb.2.2.2.2.weaken (by intro y hy; simp only [List.mem_cons, List.mem_append] at *; tauto))
        (Fr.trans (hd.2.2.2.2.weaken (by intro y hy; simp only [List.mem_cons, List.mem_append] at *; tauto))
          (he.2.2.2.2.weaken (by intro y hy; simp only [List.mem_cons, List.mem_append] at *; tauto)))
  exact hr.mono (by omega) (fun _ h => h)

end NearQuarticWires.StageCert
