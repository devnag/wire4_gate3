import Proof.Quartic.StagePullback.RowFlags

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open NativeRows

def rowRetained : List (Fin VV) := List.ofFn rowFieldRegister ++
  [Flips.leftFlag, Flips.rightFlag, transposeFlag, MarkerCalls.originalCoordinate,
    SignedCoefficients.positive, SignedCoefficients.negative]

/-- `imp:pullback`, paper/paper.tex: the retained
original row fields and its three actual source flags, before coordinate
iteration begins. -/
structure RowStored (a : DS VV MM) (r : RowRequest) : Prop where
  constants : Cst a
  fields : ∀ i : Fin 9, a.env (rowFieldRegister i) =
    r.fields[i.val]'(by rw [RowRequest.fields_length]; exact i.isLt)
  useLeft : a.env Flips.leftFlag = r.useLeft.toNat
  useRight : a.env Flips.rightFlag = r.useRight.toNat
  transpose : a.env transposeFlag = r.transpose.toNat
  coordinate : a.env MarkerCalls.originalCoordinate = 0
  positive : a.env SignedCoefficients.positive = 0
  negative : a.env SignedCoefficients.negative = 0

/-- `imp:pullback`, paper/paper.tex: literal geometry
computations preserve every original scalar row input and both initially
zero affine accumulators. -/
theorem RowStored.frame {a b : DS VV MM} {r : RowRequest} {T : List (Fin VV)}
    (h : RowStored a r) (hf : Fr a b T) (hc : Cst b)
    (hkeep : ∀ x ∈ rowRetained, x ∉ T) : RowStored b r := by
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hf _ (hkeep _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)))).trans (h.fields i)
  · exact (hf _ (hkeep _ (by simp [rowRetained]))).trans h.useLeft
  · exact (hf _ (hkeep _ (by simp [rowRetained]))).trans h.useRight
  · exact (hf _ (hkeep _ (by simp [rowRetained]))).trans h.transpose
  · exact (hf _ (hkeep _ (by simp [rowRetained]))).trans h.coordinate
  · exact (hf _ (hkeep _ (by simp [rowRetained]))).trans h.positive
  · exact (hf _ (hkeep _ (by simp [rowRetained]))).trans h.negative

/-- `imp:pullback`, paper/paper.tex: the actual
original row fields and physically formed geometry comprise the complete
canonical native-row input state. -/
structure RowPrepared (a : DS VV MM) (r : RowRequest) : Prop where
  stored : RowStored a r
  blockWidth : a.env Offsets.blockWidth = r.parameters.b
  radix : a.env Digits.radix = 2 ^ r.parameters.s
  half : a.env Flips.halfCount = r.parameters.r / 2
  leftEnd : a.env Sides.leftEnd = r.parameters.r / 2 * r.parameters.b
  blockedEnd : a.env Sides.blockedEnd = r.parameters.r * r.parameters.b
  freeLeftEnd : a.env Sides.freeLeftEnd =
    r.parameters.r * r.parameters.b + (r.parameters.n - r.parameters.r * r.parameters.b + 1) / 2
  width : a.env nativeWidth = PrimT.C4Geo.width r.parameters
  leftCount : a.env NativeRows.leftCount =
    (rowNumbers r.point r.child r.transpose true r.parameters.n).length
  rightCount : a.env NativeRows.rightCount =
    (rowNumbers r.point r.child r.transpose false r.parameters.n).length

/-- `imp:pullback`, paper/paper.tex: the prepared
original row provides precisely the actual canonical per-coordinate
translation/error input, without an extra decoded side or flip array. -/
theorem RowPrepared.inputs {a : DS VV MM} {r : RowRequest} (h : RowPrepared a r) :
    Flips.Inputs a r.point (firstCoordinate r.point) := by
  refine ⟨h.stored.constants, ?_, ?_, ?_, ?_, h.stored.useLeft, h.stored.useRight,
    h.half, h.stored.coordinate, h.blockWidth, h.radix⟩
  · simpa [VV, rowFieldRegister, RowRequest.fields, RowRequest.point] using h.stored.fields 3
  · simpa [VV, rowFieldRegister, RowRequest.fields, RowRequest.point] using h.stored.fields 6
  · simpa [VV, rowFieldRegister, RowRequest.fields, RowRequest.point] using h.stored.fields 7
  · simpa [VV, rowFieldRegister, RowRequest.fields, RowRequest.point] using h.stored.fields 8

/-- `imp:pullback`, paper/paper.tex: complete physical
original-row setup, including actual header decoding and all native side
boundaries, counts and transposition. -/
def rowSetupProgram : St VV MM :=
  .seq rowFieldsProgram (.seq rowFlagsProgram (.seq metadataProgram
    (.seq Sides.boundsProgram (.seq nativeWidthProgram countsProgram))))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: original source bytes alone physically construct the
complete native-row input, leaving the cursor at the unmodified original
signed row body and preserving both initially empty stores. -/
theorem rowSetup_run (C : Ctx) (a : DS VV MM) (r : RowRequest)
    (hc : Cst a) (hip : a.ip = 0) (hzero : a.env MarkerCalls.originalCoordinate = 0)
    (hp0 : a.env SignedCoefficients.positive = 0) (hn0 : a.env SignedCoefficients.negative = 0)
    (hinput : C.inp = r.word) (hwidth : r.Lout + 4 ≤ C.Wd) :
    Hs C rowSetupProgram a (500 * (r.Lout + 2)) (fun b =>
      RowPrepared b r ∧ b.ip = (r.fields.flatMap natWord).length + 3 ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)) := by
  have hdim : r.parameters.n + 4 ≤ C.Wd := by unfold RowRequest.Lout at hwidth; omega
  have hb : r.parameters.b ≤ r.parameters.n :=
    (Nat.le_mul_of_pos_left _ r.parameters.r_pos).trans r.parameters.r_mul_b_le
  have hs : r.parameters.s ≤ r.Lout := by
    have hh := r.parameters.s_le_b.trans hb
    unfold RowRequest.Lout
    omega
  have hcost := rowFields_cost r
  unfold rowSetupProgram
  refine Hx.hs (Hs.then (rowFields_parse C a r hc hip hinput hwidth)
    (fun b ⟨hfields, hbip, hbrest, hbc, hbfr⟩ n1 hn1 => ?_))
  have hflags : C.inp.drop b.ip = [r.useLeft, r.useRight, r.transpose] ++ r.body := by
    rw [hinput, hbip]
    simp [RowRequest.word]
  refine Hs.then (rowFlagsProgram_run C b r.useLeft r.useRight r.transpose r.body hflags)
    (fun c hflags n2 hn2 => ?_)
  subst hflags
  let c := rowFlagsState b r.useLeft r.useRight r.transpose
  have hcf := rowFlagsState_frame b r.useLeft r.useRight r.transpose
  have hcc : Cst c := hbc.of_fr hcf (by decide)
  have hcs : RowStored c r := by
    refine ⟨hcc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hcf _ (by fin_cases i <;> decide)).trans (hfields i)
    · simp only [c, rowFlagsState,
        DS.set_env_ne _ _ (by decide : Flips.leftFlag ≠ transposeFlag),
        DS.set_env_ne _ _ (by decide : Flips.leftFlag ≠ Flips.rightFlag), DS.set_env_self]
    · simp only [c, rowFlagsState,
        DS.set_env_ne _ _ (by decide : Flips.rightFlag ≠ transposeFlag), DS.set_env_self]
    · simp only [c, rowFlagsState, DS.set_env_self]
    · exact (hcf _ (by decide)).trans ((hbfr _ (by decide)).trans hzero)
    · exact (hcf _ (by decide)).trans ((hbfr _ (by decide)).trans hp0)
    · exact (hcf _ (by decide)).trans ((hbfr _ (by decide)).trans hn0)
  have h20 : c.env 20 = r.parameters.n := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hcs.fields 0
  have h21 : c.env 21 = r.parameters.r := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hcs.fields 3
  have h22 : c.env 22 = r.parameters.b := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hcs.fields 4
  have h23 : c.env 23 = r.parameters.s := by
    simpa [VV, rowFieldRegister, RowRequest.fields] using hcs.fields 5
  refine Hs.then (metadataProgram_run C c r.parameters hcc h22 h23 h21 hdim)
    (fun d ⟨hdb, hdr, hdh, hdsh, hdfr⟩ n3 hn3 => ?_)
  have hdc : Cst d := hcc.of_fr hdfr (by decide)
  have hds := hcs.frame hdfr hdc (by decide)
  have hd20 : d.env 20 = r.parameters.n := (hdfr _ (by decide)).trans h20
  have hd21 : d.env 21 = r.parameters.r := (hdfr _ (by decide)).trans h21
  have hd22 : d.env 22 = r.parameters.b := (hdfr _ (by decide)).trans h22
  refine Hs.then (Sides.boundsProgram_run C d r.parameters hd20 hd21 hd22 hdh hdim)
    (fun e ⟨hel, heb, hef, hesh, hefr⟩ n4 hn4 => ?_)
  have hec : Cst e := hdc.of_fr hefr (by decide)
  have hes := hds.frame hefr hec (by decide)
  refine Hs.then (nativeWidthProgram_run C e r.parameters hel heb hef hdim)
    (fun f ⟨hfw, hfsh, hffr⟩ n5 hn5 => ?_)
  have hfc : Cst f := hec.of_fr hffr (by decide)
  have hfs := hes.frame hffr hfc (by decide)
  have hf20 : f.env 20 = r.parameters.n :=
    (hffr _ (by decide)).trans ((hefr _ (by decide)).trans hd20)
  refine Hs.last (countsProgram_run C f r.parameters r.transpose hfc hf20 hfw hfs.transpose) ?_
  rintro g ⟨hgl, hgr, hgsh, hgfr⟩ n6 hn6
  have hgc : Cst g := hfc.of_fr hgfr (by decide)
  have hgs := hfs.frame hgfr hgc (by decide)
  have hgb : g.env Offsets.blockWidth = r.parameters.b :=
    (hgfr _ (by decide)).trans ((hffr _ (by decide)).trans ((hefr _ (by decide)).trans hdb))
  have hgrad : g.env Digits.radix = 2 ^ r.parameters.s :=
    (hgfr _ (by decide)).trans ((hffr _ (by decide)).trans ((hefr _ (by decide)).trans hdr))
  have hgh : g.env Flips.halfCount = r.parameters.r / 2 :=
    (hgfr _ (by decide)).trans ((hffr _ (by decide)).trans ((hefr _ (by decide)).trans hdh))
  have hglb : g.env Sides.leftEnd = r.parameters.r / 2 * r.parameters.b :=
    (hgfr _ (by decide)).trans ((hffr _ (by decide)).trans hel)
  have hgbb : g.env Sides.blockedEnd = r.parameters.r * r.parameters.b :=
    (hgfr _ (by decide)).trans ((hffr _ (by decide)).trans heb)
  have hgfb : g.env Sides.freeLeftEnd =
      r.parameters.r * r.parameters.b + (r.parameters.n - r.parameters.r * r.parameters.b + 1) / 2 :=
    (hgfr _ (by decide)).trans ((hffr _ (by decide)).trans hef)
  have hgw : g.env nativeWidth = PrimT.C4Geo.width r.parameters := (hgfr _ (by decide)).trans hfw
  have hlenL : (rowNumbers r.point r.child r.transpose true r.parameters.n).length =
      (if r.transpose then r.parameters.n - PrimT.C4Geo.width r.parameters else PrimT.C4Geo.width r.parameters) := by
    have hh := rowNumbers_length r.point r.child r.transpose true
    cases ht : r.transpose <;> simpa [RowRequest.point, ht] using hh
  have hlenR : (rowNumbers r.point r.child r.transpose false r.parameters.n).length =
      (if r.transpose then PrimT.C4Geo.width r.parameters else r.parameters.n - PrimT.C4Geo.width r.parameters) := by
    have hh := rowNumbers_length r.point r.child r.transpose false
    cases ht : r.transpose <;> simpa [RowRequest.point, ht] using hh
  have hgp : RowPrepared g r := ⟨hgs, hgb, hgrad, hgh, hglb, hgbb, hgfb, hgw,
    hgl.trans hlenL.symm, hgr.trans hlenR.symm⟩
  have hsame := Same.of_sh (hgsh.trans (hfsh.trans (hesh.trans hdsh)))
  have hgip : g.ip = (r.fields.flatMap natWord).length + 3 := by
    rw [hsame.ip]
    change b.ip + 3 = _
    rw [hbip]
  have hgrest : (g.out, g.ram, g.rc, g.kin, g.kout, g.kc) =
      (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) := by
    rw [hsame.out, hsame.ram, hsame.rc, hsame.kin, hsame.kout, hsame.kc]
    exact hbrest
  exact ⟨⟨hgp, hgip, hgrest⟩, by omega⟩

end NearQuarticWires.StagePullback
