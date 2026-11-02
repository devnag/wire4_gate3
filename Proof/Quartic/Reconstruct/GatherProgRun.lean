import Proof.Quartic.Reconstruct.GatherProgMain

/-!
# The gathering program: the whole run

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`gatherS` sets the constants, copies the context (`ctxS`), writes the number of listed systems (`headG`), runs every
group (`groupsS`) and closes the frame. `gatherS_run`: on the numbers of the context, the number `m` of tables and
the numbers of the groups, it writes the framed numbers of the context, `(m / tg / 2)·n_c` and the outputs of the
groups.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.Reconstruct

variable {C : Ctx}

/-! ## The number of systems -/

/-- Read `m`; `gGN := m / tg`; write `(m / tg / 2)·n_c`. -/
def headG : St VV MM := .seq (rdTo gM) (.seq (.op (.dm gM gTG gGN gQ)) (.seq (.op (.copy gMs gGN))
  (.seq (.op (.half gMs)) (.seq (.op (.mul gMs gCC t3)) (emitNatD 1)))))

/-- The variables written by `headG`. -/
def headT : List (Fin VV) := [gM, gGN, gQ, gMs, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vJ]

theorem headG_spec (a : DS VV MM) (hc : Cst a) (m tg nc : ℕ) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (m :: vs).flatMap natWord ++ rest) (hTG : a.env gTG = tg) (htg0 : 0 < tg)
    (hCC : a.env gCC = nc) (ℓ : ℕ) (hm : natBitLength m ≤ ℓ) (hms : natBitLength (m / tg / 2 * nc) ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) (htg2 : 2 * tg ≤ 2 ^ C.Wd) (hmsW : m / tg / 2 * nc < 2 ^ C.Wd) :
    Hs C headG a (2 * unitC ℓ + 10)
      (fun b => Ran a b (natWord m).length (marksD 1 (natWord (m / tg / 2 * nc))) headT [] ∧ b.env gGN = m / tg ∧
        Cst b ∧ C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  refine Hx.hs (Hs.then (rdX_spec gM (by decide) a hc m vs rest hin ℓ hm hℓ) (fun b1 ⟨e1, _, r1, c1, i1⟩ n1 hn1 => ?_))
  have b1T : b1.env gTG = tg := by rw [r1.fr gTG (by decide), hTG]
  refine Hs.then (hs_dm C gM gTG gGN gQ b1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b1T]; exact htg0) (by rw [b1T]; exact htg2)) (fun b2 hb2 n2 hn2 => ?_)
  have b2G : b2.env gGN = m / tg := by
    rw [hb2, DS.set_env_ne _ _ (show gGN ≠ gQ by decide), DS.set_env_self, e1, b1T]
  have b2f : ∀ y, y ≠ gGN → y ≠ gQ → b2.env y = b1.env y := fun y h1 h2 => by
    rw [hb2, DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
  refine Hs.then (hs_copy C gMs gGN b2 (by decide)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_half C gMs _) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (hs_mul C gMs gCC t3 _ (by decide) (by decide) (by decide) (by
    simp only [DS.set_env_self, DS.set_env_ne _ _ (show gCC ≠ gMs by decide), b2G]
    rw [b2f gCC (by decide) (by decide), r1.fr gCC (by decide), hCC]; exact hmsW)) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  set b4 := (b2.set gMs (b2.env gGN)).set gMs ((b2.set gMs (b2.env gGN)).env gMs / 2) with hb4
  have b5t : (b4.set t3 (b4.env gMs * b4.env gCC)).env t3 = m / tg / 2 * nc := by
    rw [DS.set_env_self, hb4, DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (show gCC ≠ gMs by decide),
      DS.set_env_ne _ _ (show gCC ≠ gMs by decide), b2G, b2f gCC (by decide) (by decide), r1.fr gCC (by decide), hCC]
  have c5 : Cst (b4.set t3 (b4.env gMs * b4.env gCC)) := by
    rw [hb4]; exact cst_set (cst_set (cst_set (by rw [hb2]; exact cst_set (cst_set c1 _ (by decide)) _ (by decide))
      _ (by decide)) _ (by decide)) _ (by decide)
  refine Hs.last (emN_spec _ c5 ℓ (by rw [b5t]; exact hms) hℓ) (fun b6 ⟨r6, c6⟩ n6 hn6 => ?_)
  have r5 : Ran b1 (b4.set t3 (b4.env gMs * b4.env gCC)) 0 [] headT [] := by
    rw [hb4, hb2]
    exact (((((Ran.refl b1 headT []).set _ (by decide)).set _ (by decide)).set _ (by decide)).set _
      (by decide)).set _ (by decide)
  refine ⟨⟨?_, by rw [r6.fr gGN (by decide), DS.set_env_ne _ _ (show gGN ≠ t3 by decide), hb4,
    DS.set_env_ne _ _ (show gGN ≠ gMs by decide), DS.set_env_ne _ _ (show gGN ≠ gMs by decide), b2G], c6, ?_⟩, ?_⟩
  · have hr := ((r1.weaken (fun y hy => by revert y; decide) (fun _ h => h)).trans r5).trans
      (r6.weaken (fun y hy => by revert y; decide) (fun _ h => h))
    exact hr.eqk (by simp) (by rw [b5t]; simp)
  · simp only [r6.ip, r5.ip, Nat.add_zero]; exact i1
  · omega

/-! ## The groups -/

/-- The conditions on one group of a run. -/
structure GrpOK (C : Ctx) (ℓ D tg : ℕ) (bits : List ℕ) (g : GrpD) : Prop where
  ne : g.rows ≠ []
  len : g.rows.length = tg
  dl : g.dl.length = D
  ents : ∀ r ∈ g.rows, r.2.2.2.length = bits.length
  v : ∀ v ∈ g.nats, natBitLength v ≤ ℓ
  vC : ∀ x ∈ cfOf g bits, natBitLength x ≤ ℓ
  W : tg * ncOf bits * pwOf g bits < 2 ^ C.Wd
  Wp : 2 * pwOf g bits ≤ 2 ^ C.Wd
  pat : g.pat.sum + g.pat.length < 2 ^ C.Wd

/-- Run every group. -/
def groupsS : St VV MM := .seq (.op (.zero gGI)) (.loop (.lt gGI gGN) groupS)

theorem groupsS_spec (a : DS VV MM) (hc : Cst a) (Gs : List GrpD) (bits vs : List ℕ) (rest : List Bool)
    (ℓ D tg GC : ℕ) (hin : C.inp.drop a.ip = (Gs.flatMap GrpD.nats ++ vs).flatMap natWord ++ rest)
    (hok : ∀ g ∈ Gs, GrpOK C ℓ D tg bits g) (hcost : ∀ g ∈ Gs, grpCost ℓ g bits ≤ GC)
    (hGN : a.env gGN = Gs.length) (hTG : a.env gTG = tg) (hCC : a.env gCC = ncOf bits)
    (hZ : a.ram sZc = bits) (hZc : a.rc sZc ≤ bits.length)
    (hHd : (a.ram sHd).length ≤ 2 * D) (hHdc : a.rc sHd ≤ 2 * D)
    (hIl : (a.ram sI).length ≤ 3 * tg) (hIc : a.rc sI ≤ 3 * tg)
    (hCl : (a.ram sC).length ≤ tg * ncOf bits) (hCc : a.rc sC ≤ tg * ncOf bits)
    (hRl : (a.ram sR).length ≤ tg * ncOf bits) (hRc : a.rc sR ≤ tg * ncOf bits)
    (h2ℓ : 2 ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hvT : natBitLength tg ≤ ℓ) (hWn : 2 * ncOf bits ≤ 2 ^ C.Wd)
    (hdl : D < 2 ^ C.Wd) (htg : tg < 2 ^ C.Wd) (hnc : ncOf bits < 2 ^ C.Wd) (hGs : Gs.length < 2 ^ C.Wd) :
    Hs C groupsS a (Gs.length * (GC + 2) + 4)
      (fun b => Ran a b ((Gs.flatMap GrpD.nats).flatMap natWord).length
        (marksD 1 ((Gs.flatMap (grpOut · bits)).flatMap natWord)) stepT stepM ∧ Cst b ∧
        C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  let I : ℕ → DS VV MM → Prop := fun i b => b.env gGI = i ∧ b.env gGN = Gs.length ∧ b.env gTG = tg ∧
    b.env gCC = ncOf bits ∧ b.ram sZc = bits ∧ b.rc sZc ≤ bits.length ∧
    (b.ram sHd).length ≤ 2 * D ∧ b.rc sHd ≤ 2 * D ∧ (b.ram sI).length ≤ 3 * tg ∧ b.rc sI ≤ 3 * tg ∧
    (b.ram sC).length ≤ tg * ncOf bits ∧ b.rc sC ≤ tg * ncOf bits ∧
    (b.ram sR).length ≤ tg * ncOf bits ∧ b.rc sR ≤ tg * ncOf bits ∧
    Ran a b (((Gs.take i).flatMap GrpD.nats).flatMap natWord).length
      (marksD 1 (((Gs.take i).flatMap (grpOut · bits)).flatMap natWord)) stepT stepM ∧ Cst b ∧
    C.inp.drop b.ip = ((Gs.drop i).flatMap GrpD.nats ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) gGI gGN (by decide) groupS Gs.length GC I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
    intro i hi b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
    have hmem : Gs[i] ∈ Gs := List.getElem_mem hi
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := hok _ hmem
    have hd : Gs.drop i = Gs[i] :: Gs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have hin1 : C.inp.drop b.ip = (Gs[i].nats ++ ((Gs.drop (i + 1)).flatMap GrpD.nats ++ vs)).flatMap natWord ++
        rest := by rw [h17, hd, List.flatMap_cons, List.append_assoc]
    refine (groupS_spec b h16 Gs[i] bits _ rest hin1 o1 (by rw [h3, o2]) h4 i h1 h5 h6 o4 (by rw [o3]; exact h7)
      (by rw [o3]; exact h8) (by rw [o2]; exact h9) (by rw [o2]; exact h10) (by rw [o2]; exact h11)
      (by rw [o2]; exact h12) (by rw [o2]; exact h13) (by rw [o2]; exact h14) ℓ h2ℓ hℓ o5 o6 (by rw [o2]; exact hvT)
      (by rw [o2]; exact o7) hWn o8 o9 (by rw [o3]; exact hdl) (by rw [o2]; exact htg) hnc (by omega)).mono
      (hcost _ hmem) ?_
    rintro d ⟨r1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, c1, i1⟩
    rw [o2] at e6 e7 e8 e9 e10 e11
    rw [o3] at e4 e5
    refine ⟨e1, by rw [r1.fr gGN (by decide), h2], by rw [r1.fr gTG (by decide), h3],
      by rw [r1.fr gCC (by decide), h4], e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, ?_, c1, by simpa using i1⟩
    refine (h15.trans r1).eqk ?_ ?_
    · rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.flatMap_singleton, List.flatMap_append,
        List.length_append]
    · rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.flatMap_singleton, List.flatMap_append,
        marksD_append])
  refine Hx.hs (Hs.then (hs_zero C gGI a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨by vsimp [], by vsimp [hGN], by vsimp [hTG], by vsimp [hCC], hZ, hZc, hHd, hHdc, hIl, hIc,
    hCl, hCc, hRl, hRc, ((Ran.refl a stepT stepM).set (x := gGI) 0 (by decide)).eqk (by simp) (by simp [marksD]),
    cst_set hc _ (by decide), by simpa using hin⟩)
    (fun b ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h15, h16, h17⟩ n hn => ⟨⟨?_, h16, by simpa using h17⟩, by omega⟩)
  rw [List.take_length] at h15; exact h15

/-! ## The whole program -/

/-- **The gathering program.** -/
def gatherS : St VV MM :=
  .seq NearCubicGates.Close.CounterMachine.PrefixProg.cstInit (.seq ctxS (.seq headG (.seq groupsS (putD 0 false))))

/-- The cost of the whole run. -/
def gatherCost (ℓ nf nb ng GC : ℕ) : ℕ := ctxCost ℓ nf nb + 2 * unitC ℓ + ng * (GC + 2) + 30

theorem gatherS_run (C : Ctx) (pre5 fs mid4 : List ℕ) (h5 : pre5.length = 5) (h4 : mid4.length = 4) (tg : ℕ)
    (bits : List ℕ) (m : ℕ) (Gs : List GrpD) (ℓ D GC : ℕ)
    (hinp : C.inp = (ctxNats pre5 fs mid4 tg bits ++ m :: Gs.flatMap GrpD.nats).flatMap natWord)
    (hok : ∀ g ∈ Gs, GrpOK C ℓ D tg bits g) (hcost : ∀ g ∈ Gs, grpCost ℓ g bits ≤ GC)
    (htg0 : 0 < tg) (hGN : m / tg = Gs.length) (hsum : bits.sum = ncOf bits)
    (h2ℓ : 2 ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) (hvc : ∀ v ∈ ctxNats pre5 fs mid4 tg bits, natBitLength v ≤ ℓ)
    (hm : natBitLength m ≤ ℓ) (hms : natBitLength (m / tg / 2 * ncOf bits) ≤ ℓ)
    (hWn : 2 * ncOf bits ≤ 2 ^ C.Wd) (hWt : 2 * tg ≤ 2 ^ C.Wd) (hWb : bits.sum + bits.length < 2 ^ C.Wd)
    (hfs : fs.length < 2 ^ C.Wd) (hmsW : m / tg / 2 * ncOf bits < 2 ^ C.Wd)
    (hdl : D < 2 ^ C.Wd) (hnc : ncOf bits < 2 ^ C.Wd) (hGs : Gs.length < 2 ^ C.Wd) :
    Hs C gatherS (a0 : DS VV MM) (gatherCost ℓ fs.length bits.length Gs.length GC)
      (fun b => b.out = marksD 1 ((ctxNats pre5 fs mid4 tg bits ++ (m / tg / 2 * ncOf bits) ::
        Gs.flatMap (grpOut · bits)).flatMap natWord) ++ [false]) := by
  have hvT : natBitLength tg ≤ ℓ := hvc tg (by simp [ctxNats])
  have htgW : tg < 2 ^ C.Wd := by omega
  refine Hx.hs (Hs.then (NearCubicGates.Close.CounterMachine.PrefixProg.cstInit_spec C (by omega))
    (fun d ⟨cd, dram, drc, dip, dout, _, _, _⟩ n0 hn0 => ?_))
  have hin : C.inp.drop d.ip = (ctxNats pre5 fs mid4 tg bits ++ (m :: Gs.flatMap GrpD.nats)).flatMap natWord ++ [] := by
    rw [dip, List.drop_zero, hinp, List.append_nil]
  refine Hs.then (ctxS_spec d cd pre5 fs mid4 h5 h4 tg bits _ [] hin (by rw [dram]) (by rw [drc]) ℓ hvc hℓ hWb hfs)
    (fun b1 ⟨r1, e1, e2, e3, e4, c1, i1⟩ n1 hn1 => ?_)
  refine Hs.then (headG_spec b1 c1 m tg (ncOf bits) _ [] i1 e1 htg0 (by rw [e2, hsum]) ℓ hm hms hℓ hWt hmsW)
    (fun b2 ⟨r2, e5, c2, i2⟩ n2 hn2 => ?_)
  have b2s : ∀ s : Fin MM, b2.ram s = b1.ram s ∧ b2.rc s = b1.rc s := fun s => ⟨r2.ram s (by simp), r2.rc s (by simp)⟩
  have b1s : ∀ s : Fin MM, s ≠ sZc → b1.ram s = [] ∧ b1.rc s = 0 := fun s hs => by
    have h : s ∉ [sZc] := by simpa using hs
    rw [r1.ram s h, r1.rc s h, dram, drc]; exact ⟨rfl, rfl⟩
  refine Hs.then (groupsS_spec b2 c2 Gs bits [] [] ℓ D tg GC (by simpa using i2) hok hcost (by rw [e5, hGN])
    (by rw [r2.fr gTG (by decide), e1]) (by rw [r2.fr gCC (by decide), e2, hsum]) (by rw [(b2s sZc).1, e3])
    (by rw [(b2s sZc).2, e4]) (by rw [(b2s sHd).1, (b1s sHd (by decide)).1]; simp)
    (by rw [(b2s sHd).2, (b1s sHd (by decide)).2]; simp) (by rw [(b2s sI).1, (b1s sI (by decide)).1]; simp)
    (by rw [(b2s sI).2, (b1s sI (by decide)).2]; simp) (by rw [(b2s sC).1, (b1s sC (by decide)).1]; simp)
    (by rw [(b2s sC).2, (b1s sC (by decide)).2]; simp) (by rw [(b2s sR).1, (b1s sR (by decide)).1]; simp)
    (by rw [(b2s sR).2, (b1s sR (by decide)).2]; simp) h2ℓ hℓ hvT hWn hdl htgW hnc hGs)
    (fun b3 ⟨r3, c3, _⟩ n3 hn3 => ?_)
  refine Hs.last (putD_spec 0 false b3) (fun b4 w4 n4 hn4 => ⟨?_, ?_⟩)
  · rw [w4.out, r3.out, r2.out, r1.out, dout]
    simp only [List.flatMap_append, List.flatMap_cons, marksD_append, List.nil_append, List.append_assoc]
    rfl
  · have : 2 * 2 ^ 0 + 1 = 3 := by norm_num
    rw [this] at hn4
    unfold gatherCost
    omega

end NearQuarticWires.Reconstruct.GatherProg
