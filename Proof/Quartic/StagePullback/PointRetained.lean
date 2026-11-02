import Proof.Quartic.StagePullback.PointSetup

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm` and `imp:pullback`, paper/paper.tex: the actual point parser retains all
nine source scalars alongside complete affine coordinate metadata. -/
theorem pointSetup_prefix_fields (C : Ctx) (a : DS VV MM) (q : PointRequest) (rest : List Bool)
    (x : Fin q.parameters.n) (hc : Cst a) (hip : a.ip = 0)
    (hcoord : a.env MarkerCalls.originalCoordinate = x.val)
    (hinput : C.inp = q.word ++ rest) (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C pointSetupProgram a (400 * (q.parameters.n + 2)) (fun b =>
      (∀ i : Fin 9, b.env (pointFieldRegister i) =
        q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt)) ∧
      Flips.Inputs b q x ∧ b.ip = q.word.length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)) := by
  have hcost := StageGamma.readFieldsCost_le q.fields (q.parameters.n + 1)
    (fun v hv => q.fields_bitLength v hv)
  rw [PointRequest.fields_length] at hcost
  have hb : q.parameters.b ≤ q.parameters.n :=
    (Nat.le_mul_of_pos_left _ q.parameters.r_pos).trans q.parameters.r_mul_b_le
  have hs : q.parameters.s ≤ q.parameters.n := q.parameters.s_le_b.trans hb
  unfold pointSetupProgram
  refine Hx.hs (Hs.then (pointFields_prefix C q ([q.useLeft, q.useRight] ++ rest)
    (by rw [hinput, ← q.fields_word, List.append_assoc]) (by omega) a hc hip)
    (fun b ⟨hbfields, hbip, hbrest, hbc, hbfr⟩ n1 hn1 => ?_))
  have hflags : C.inp.drop b.ip = [q.useLeft, q.useRight] ++ rest := by
    rw [hinput, hbip, ← q.fields_word]
    simp
  refine Hs.then (flagsProgram_run C b q.useLeft q.useRight rest hflags)
    (fun c hcflags n2 hn2 => ?_)
  subst hcflags
  let c := flagsState b q.useLeft q.useRight
  have hcf := flagsState_frame b q.useLeft q.useRight
  have hcc : Cst c := hbc.of_fr hcf (by decide)
  have hcflds (i : Fin 9) : c.env (pointFieldRegister i) =
      q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt) := by
    rw [hcf _ (by fin_cases i <;> decide)]
    exact hbfields i
  have h22 : c.env 22 = q.parameters.b := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hcflds 2
  have h23 : c.env 23 = q.parameters.s := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hcflds 3
  have h21 : c.env 21 = q.parameters.r := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hcflds 1
  refine Hs.last (metadataProgram_run C c q.parameters hcc h22 h23 h21 hwidth) ?_
  rintro d ⟨hdb, hdr, hdh, hdsh, hdfr⟩ n3 hn3
  have hdflds (i : Fin 9) : d.env (pointFieldRegister i) =
      q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt) := by
    rw [hdfr _ (by fin_cases i <;> decide)]
    exact hcflds i
  have hdc : Cst d := hcc.of_fr hdfr (by decide)
  have hdcoord : d.env MarkerCalls.originalCoordinate = x.val :=
    (hdfr _ (by decide)).trans ((hcf _ (by decide)).trans
      ((hbfr _ (by decide)).trans hcoord))
  have hil : d.env Flips.leftFlag = q.useLeft.toNat := by
    rw [hdfr _ (by decide)]
    simp only [c, flagsState, DS.set_env_ne _ _ (by decide : Flips.leftFlag ≠ Flips.rightFlag),
      DS.set_env_self]
  have hir : d.env Flips.rightFlag = q.useRight.toNat := by
    rw [hdfr _ (by decide)]
    simp only [c, flagsState, DS.set_env_self]
  have hdinput : Flips.Inputs d q x := ⟨hdc,
    by simpa [VV, pointFieldRegister, PointRequest.fields] using hdflds 1,
    by simpa [VV, pointFieldRegister, PointRequest.fields] using hdflds 4,
    by simpa [VV, pointFieldRegister, PointRequest.fields] using hdflds 7,
    by simpa [VV, pointFieldRegister, PointRequest.fields] using hdflds 8,
    hil, hir, hdh, hdcoord, hdb, hdr⟩
  have hdip : d.ip = q.word.length := by
    rw [(Same.of_sh hdsh).ip]
    change b.ip + 2 = q.word.length
    rw [hbip, ← q.fields_word]
    simp
  have hdrest : (d.out, d.ram, d.rc, d.kin, d.kout, d.kc) =
      (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) := by
    have hds := Same.of_sh hdsh
    rw [hds.out, hds.ram, hds.rc, hds.kin, hds.kout, hds.kc]
    exact hbrest
  exact ⟨⟨hdflds, hdinput, hdip, hdrest⟩, by omega⟩

end NearQuarticWires.StagePullback
