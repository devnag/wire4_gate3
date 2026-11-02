import Proof.Quartic.Reconstruct.PrintRun1

/-!
# The run of the printing stage: the tables

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

After the context, `printPostS` sets the constants of the request phase, writes the number of tables at depth `1`,
runs the loop nest over the parts, patterns, digit vectors, primes and residue vectors (`PrintNest3.partS_spec`) and
writes the end mark (`printPostS_spec`). `printsS_run`: the whole stage prints `frame (printsWord q)`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord kindTag callWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {C : Ctx} {B1 B2 : ℕ}

/-- The constants, the number of tables, the tables and the end mark. -/
def printPostS : St VV MM :=
  .seq setupA (.seq setupB (.seq topS (.seq setupC (.seq countS (.seq (emitV qCnt 1) (.seq partS (putD 0 false)))))))

/-- **The printing stage.** -/
def printsS : St VV MM := .seq printPreS printPostS

theorem one_le_hE (q : ChildRequest B1 B2) : 1 ≤ q.selected.1.hE := by
  have h1 := (rules q).T_pos
  have h2 := (rules q).height
  have h3 := (rules q).h_eq
  by_contra h
  have h0 : q.selected.1.hE = 0 := by omega
  rw [h0, Nat.zero_div] at h3
  omega

/-- The number of printed tables, as computed. -/
noncomputable def cntOf (q : ChildRequest B1 B2) : ℕ := 512 * baseOf q ^ (q.cellCall.J + 1) * a1Of q * tgOf q

/-- The bounds used by `printPostS`. -/
structure PostBounds (q : ChildRequest B1 B2) (W : ℕ) : Prop where
  jw : 2 * (q.cellCall.J + 1) < 2 ^ W
  w512 : 512 < 2 ^ W
  hEw : 2 * q.selected.1.hE < 2 ^ W
  top : baseOf q ^ q.cellCall.J < 2 ^ W
  c0 : 512 * baseOf q ^ (q.cellCall.J + 1) < 2 ^ W
  c1 : 512 * baseOf q ^ (q.cellCall.J + 1) * a1Of q < 2 ^ W
  c2 : cntOf q < 2 ^ W
  cb : natBitLength (cntOf q) + 2 < 2 ^ W
  a1 : a1Of q < 2 ^ W
  pW : q.selected.1.P < 2 ^ W
  rbits : ∀ v ∈ [8, 2 * (q.cellCall.J + 1), 2, baseOf q + (q.selected.1.hE - 1),
    baseOf q + (if pairBit q = 1 then q.selected.1.hE - 1 else 0)], natBitLength v ≤ W - 3
  pb : natBitLength q.selected.1.P ≤ W - 3
  one : natBitLength 1 ≤ W - 3

/-- The cost of `printPostS` at width `W`. -/
noncomputable def printPostCost (q : ChildRequest B1 B2) (W : ℕ) : ℕ :=
  q.cellCall.J * 7 + emitNatDCost 1 (natBitLength (cntOf q)) +
    2 * sigCost (rpOf q (W - 3)) (npOf q q.selected.1.P) + 90

theorem frame_printsWord (q : ChildRequest B1 B2) :
    frame (printsWord q) = marksD 2 (contextWord q) ++ bitD 1 false ++ marksD 1 (natWord (printList q).length) ++
      (printList q).flatMap reqOut ++ [false] := by
  rw [frame_eq_marksD]
  unfold printsWord listWord
  rw [marksD_append, marksD_frame, marksD_append, marksD_flatMap]
  simp only [List.append_assoc]
  rfl

/-- **The tables of the printing stage.** -/
theorem printPostS_spec (q : ChildRequest B1 B2) (b5 : DS VV MM) (hm : MidDone q b5) (hpre : PreBounds q C.Wd)
    (hB : PostBounds q C.Wd) :
    Hs C printPostS b5 (printPostCost q C.Wd)
      (fun b => b.out = b5.out ++ marksD 1 (natWord (printList q).length) ++ (printList q).flatMap reqOut ++
        [false]) := by
  have hw := hpre.w6
  refine Hx.hs (Hs.then (setupA_spec b5 hm.cst q.cellCall.J hm.jj hB.jw hB.w512.le)
    (fun b6 ⟨v8, v128, v256, vJp1, vLen, s6, f6⟩ n6 hn6 => ?_))
  have c6 : Cst b6 := Cst.of_fr hm.cst f6 (by decide)
  have e6 : ∀ y, y ∉ setupAT → b6.env y = b5.env y := f6
  refine Hs.then (setupB_spec b6 c6 q.selected.1.hE (by rw [e6 kE (by decide), hm.hE]) hB.hEw)
    (fun b7 ⟨vBase, vO0, s7, f7, c7⟩ n7 hn7 => ?_)
  have e7 : ∀ y, y ∉ setupBT → b7.env y = b6.env y := f7
  refine Hs.then (topS_spec b7 c7 (baseOf q) q.cellCall.J vBase (by rw [e7 kJ (by decide), e6 kJ (by decide), hm.jj])
    hB.top (by have := hB.jw; omega)) (fun b8 ⟨vTop, s8, f8, c8⟩ n8 hn8 => ?_)
  have e8 : ∀ y, y ∉ topT → b8.env y = b7.env y := f8
  have hpb8 : b8.env kPair = pairBit q := by
    rw [e8 kPair (by decide), e7 kPair (by decide), e6 kPair (by decide), hm.pair]
  refine Hs.then (setupC_spec b8 c8 _ (baseOf q) (q.selected.1.hE - 1) (pairBit q) vTop
    (by rw [e8 qBase (by decide), vBase]; rfl) (by rw [e8 qO0 (by decide), vO0]) hpb8
    (by rw [← pow_succ]; have := hB.c0; omega)) (fun b9 ⟨vA0, vA1, vO1, s9, f9, c9⟩ n9 hn9 => ?_)
  have e9 : ∀ y, y ∉ setupCT → b9.env y = b8.env y := f9
  have vA0' : b9.env qA0 = baseOf q ^ (q.cellCall.J + 1) := by rw [vA0, ← pow_succ]
  have vA1' : b9.env qA1 = a1Of q := by rw [vA1, ← pow_succ]; rfl
  refine Hs.then (countS_spec b9 c9 _ _ (tgOf q)
    (by rw [e9 q256 (by decide), e8 q256 (by decide), e7 q256 (by decide), v256]) vA0' vA1'
    (by rw [e9 kG (by decide), e8 kG (by decide), e7 kG (by decide), e6 kG (by decide), hm.tg]) hB.c2 hB.c1 hB.c0
    hB.w512) (fun b10 ⟨vCnt, s10, f10, c10⟩ n10 hn10 => ?_)
  have e10 : ∀ y, y ∉ [qCnt, t0, t1] → b10.env y = b9.env y := f10
  have s510 : Same b5 b10 := (((s6.trans s7).trans s8).trans s9).trans s10
  have hok10 : ∀ m, b10.rc m ≤ (b10.ram m).length := fun m => by rw [s510.rc, s510.ram]; exact hm.rcok m
  refine Hs.then (emitV_spec qCnt (by decide) 1 b10 c10 hok10 (by omega) (by rw [vCnt]; exact hB.cb))
    (fun b11 ⟨m11, c11⟩ n11 hn11 => ?_)
  have k9 : ∀ y, y ∉ emitVT ++ [qCnt, t0, t1] → b11.env y = b9.env y := fun y hy => by
    rw [m11.fr y (fun h => hy (List.mem_append_left _ h)), e10 y (fun h => hy (List.mem_append_right _ h))]
  have k7 : ∀ y, y ∉ emitVT ++ [qCnt, t0, t1] ++ setupCT ++ topT → b11.env y = b7.env y := fun y hy => by
    rw [k9 y (fun h => hy (by revert h; revert y; decide)), e9 y (fun h => hy (by revert h; revert y; decide)),
      e8 y (fun h => hy (by revert h; revert y; decide))]
  have k5 : ∀ y, y ∉ emitVT ++ [qCnt, t0, t1] ++ setupCT ++ topT ++ setupBT ++ setupAT → b11.env y = b5.env y :=
    fun y hy => by
      rw [k7 y (fun h => hy (by revert h; revert y; decide)), e7 y (fun h => hy (by revert h; revert y; decide)),
        e6 y (fun h => hy (by revert h; revert y; decide))]
  have k6 : ∀ y, y ∉ emitVT ++ [qCnt, t0, t1] ++ setupCT ++ topT ++ setupBT → b11.env y = b6.env y :=
    fun y hy => by
      rw [k7 y (fun h => hy (by revert h; revert y; decide)), e7 y (fun h => hy (by revert h; revert y; decide))]
  have ram11 : b11.ram = b5.ram := by rw [m11.ram, s510.ram]
  have hc0 := hB.c0
  have hjw := hB.jw
  have hBW : 2 * baseOf q ^ (q.cellCall.J + 1) ≤ 2 ^ C.Wd := by omega
  have hJW : q.cellCall.J + 1 < 2 ^ C.Wd := by omega
  have hA0W : baseOf q ^ (q.cellCall.J + 1) < 2 ^ C.Wd := by omega
  have hl3 : C.Wd - 3 + 3 ≤ C.Wd := by omega
  have hrp : RPok (rpOf q (C.Wd - 3)) b11 C.Wd :=
    ⟨by rw [k6 q8 (by decide), v8], by rw [k6 q128 (by decide), v128], by rw [k6 qLen (by decide), vLen]; rfl,
      by rw [k9 qTop (by decide), e9 qTop (by decide), vTop]; rfl, by rw [k7 qBase (by decide), vBase]; rfl,
      by rw [k6 qJp1 (by decide), vJp1]; rfl, by rw [k7 qO0 (by decide), vO0]; rfl,
      by rw [k9 qO1 (by decide), vO1]; rfl, by rw [k5 kPL (by decide), hm.pl]; rfl, by rw [ram11, hm.sp]; rfl,
      by rw [ram11, hm.sg]; rfl, hl3, hBW, hJW, hB.w512.le, hpre.pw, hB.rbits⟩
  have hnp : NPok (rpOf q (C.Wd - 3)) (npOf q q.selected.1.P) b11 C.Wd :=
    ⟨by rw [ram11, hm.spr]; rfl, by rw [k5 kPc (by decide), hm.npc]; rfl, by rw [k5 kPair (by decide), hm.pair]; rfl,
      fun p hp => le_P_of_mem_primes q ((Finset.mem_sort _).mp hp), one_le_P q, hB.pW, hB.pb, hpre.np,
      by rw [k9 qA0 (by decide), vA0']; rfl, by rw [k9 qA1 (by decide), vA1']; rfl,
      by rw [k6 q256 (by decide), v256], hA0W, hB.a1, rfl, Nat.succ_pos _, hB.one⟩
  have rs11 : RS b11 b11 := ⟨c11, m11.rcok, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  refine Hs.then (partS_spec _ _ b11 hrp hnp b11 rs11) (fun b12 ⟨m12, _⟩ n12 hn12 => ?_)
  refine Hs.last (putD_spec 0 false b12) (fun b13 w13 n13 hn13 => ⟨?_, ?_⟩)
  · have htg : tgOf q = tablesPerGroup q := (tablesPerGroup_eq q).symm
    rw [w13.out, m12.out, m11.out, vCnt, s510.out, printList_length_eq, printList_flatMap q (C.Wd - 3) q.selected.1.P,
      htg]
    rfl
  · have : 2 * 2 ^ 0 + 1 = 3 := by norm_num
    rw [this] at hn13
    have hcnt : b10.env qCnt = cntOf q := vCnt
    rw [hcnt] at hn11
    unfold printPostCost
    omega

/-- The cost of the printing stage at width `W`. -/
noncomputable def printRunCost (q : ChildRequest B1 B2) (W : ℕ) : ℕ := printPreCost q W + printPostCost q W + 1

/-- **The printing stage prints `frame (printsWord q)`.** -/
theorem printsS_run (q : ChildRequest B1 B2) (hinp : C.inp = gammaWord q) (hpre : PreBounds q C.Wd)
    (hpost : PostBounds q C.Wd) :
    Hs C printsS (a0 : DS VV MM) (printRunCost q C.Wd) (fun b => b.out = frame (printsWord q)) := by
  refine Hx.hs (Hs.then (printPreS_spec q hinp hpre) (fun b5 ⟨hm, o5⟩ n5 hn5 => ?_))
  refine Hs.last (printPostS_spec q b5 hm hpre hpost) (fun b ho n hn => ⟨?_, ?_⟩)
  · rw [ho, o5, frame_printsWord]
  · unfold printRunCost
    omega

end NearQuarticWires.Reconstruct
