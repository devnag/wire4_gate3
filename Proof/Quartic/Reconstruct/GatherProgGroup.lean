import Proof.Quartic.Reconstruct.GatherProgTable

/-!
# The gathering program: the tables of one group

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The tables of a group `(s, σ, δ)` share the part, the pattern and the digits and differ by the row `(p, ρ_Y)` and
the entries (`GrpD`). `tablesLoopS` reads them all (`tablesLoopS_spec`): afterwards `gS`, `gAct`, `gDn` and the
store `sHd` hold the part, the parity of the pattern and the digits, the store `sI` the rows `(p, |ρ_1|, |ρ_2|)`, and
the store `sC` the certified counts, table by table, with their sum in `gSum`.
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

/-- A row of a group: the prime, the residues and the entries of its table. -/
abbrev RowD : Type := ℕ × ℤ × ℤ × List ℤ

/-- The data of a group of tables: the part, the pattern bits, the digits, and the rows. -/
structure GrpD where
  s : ℕ
  pat : List ℕ
  dl : List ℤ
  rows : List RowD

namespace GrpD

/-- The table of a row. -/
def tbl (g : GrpD) (r : RowD) : TblD := ⟨g.s, g.pat, r.1, g.dl, r.2.1, r.2.2.1, r.2.2.2⟩

/-- The numbers of the tables of a group. -/
def nats (g : GrpD) : List ℕ := g.rows.flatMap fun r => tblNats (g.tbl r)

end GrpD

/-- The row index `(p, |ρ_1|, |ρ_2|)` kept for a row. -/
def rowI (r : RowD) : List ℕ := [r.1, r.2.1.natAbs, r.2.2.1.natAbs]

/-- The certified counts of a row. -/
def cntsOf (bits : List ℕ) (r : RowD) : List ℕ := cnts r.2.2.2 bits

theorem rowI_flatMap_length (L : List RowD) : (L.flatMap rowI).length = 3 * L.length := by
  induction L with
  | nil => rfl
  | cons r L ih => simp [rowI, ih]; omega

/-- The number of certified columns (bits `1`). -/
def ncOf (bits : List ℕ) : ℕ := (bits.filter fun b => b = 1).length

theorem cnts_length (ents : List ℤ) (bits : List ℕ) (h : ents.length = bits.length) :
    (cnts ents bits).length = ncOf bits := by
  induction ents generalizing bits with
  | nil => cases bits with
    | nil => rfl
    | cons _ _ => simp at h
  | cons e ents ih => cases bits with
    | nil => simp at h
    | cons b bits =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      unfold cnts ncOf at *
      simp only [List.zip_cons_cons, List.filterMap_cons, List.filter_cons]
      have := ih bits h
      split_ifs <;> simp_all

theorem cntsOf_flatMap_length (bits : List ℕ) (L : List RowD) (hL : ∀ r ∈ L, r.2.2.2.length = bits.length) :
    (L.flatMap (cntsOf bits)).length = ncOf bits * L.length := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [ih (fun r' h => hL r' (List.mem_cons_of_mem _ h)), cntsOf, cnts_length _ _ (hL r List.mem_cons_self)]
    ring

/-! ## The tables loop -/

/-- Read the `gTG` tables of a group. -/
def tablesLoopS : St VV MM := .seq (.op (.zero gTk)) (.loop (.lt gTk gTG) (.seq tableS (.op (.inc gTk))))

/-- The variables written by `tablesLoopS`. -/
def grpT : List (Fin VV) := gTk :: tblT

/-- The cost of one table of a group, uniform over its rows. -/
def tblCostU (ℓ np nd nb : ℕ) : ℕ := 2 * nd + nb + (np + 2 * nd + 2 * nb + 12) * (unitC ℓ + 10)

theorem tablesLoopS_spec (a : DS VV MM) (hc : Cst a) (g : GrpD) (bits vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = (g.nats ++ vs).flatMap natWord ++ rest) (hne : g.rows ≠ [])
    (hTG : a.env gTG = g.rows.length)
    (hZ : a.ram sZc = bits) (hZc : a.rc sZc ≤ bits.length)
    (hbl : ∀ r ∈ g.rows, r.2.2.2.length = bits.length)
    (hHd : (a.ram sHd).length ≤ 2 * g.dl.length) (hHdc : a.rc sHd ≤ 2 * g.dl.length)
    (oI : List ℕ) (hI : a.ram sI = oI) (hIc : a.rc sI = 0)
    (oC : List ℕ) (hCr : a.ram sC = oC) (hCc : a.rc sC = 0) (hσ : a.env gSum = 0)
    (ℓ : ℕ) (hv : ∀ v ∈ g.nats, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hs : (g.rows.flatMap (cntsOf bits)).sum < 2 ^ C.Wd) (hpat : g.pat.sum + g.pat.length < 2 ^ C.Wd)
    (hdl : g.dl.length < 2 ^ C.Wd) (htg : g.rows.length < 2 ^ C.Wd) :
    Hs C tablesLoopS a (g.rows.length * (tblCostU ℓ g.pat.length g.dl.length bits.length + 4) + 4)
      (fun b => b.env gS = g.s ∧ b.env gAct = g.pat.sum % 2 ∧ b.env gDn = g.dl.length ∧
        b.env gTG = g.rows.length ∧ b.env gSum = (g.rows.flatMap (cntsOf bits)).sum ∧
        b.ram sHd = g.dl.flatMap intNats ∧ b.rc sHd = 2 * g.dl.length ∧
        b.ram sI = ovw oI (g.rows.flatMap rowI) ∧ b.rc sI = (g.rows.flatMap rowI).length ∧
        b.ram sC = ovw oC (g.rows.flatMap (cntsOf bits)) ∧ b.rc sC = (g.rows.flatMap (cntsOf bits)).length ∧
        b.ram sZc = bits ∧ b.rc sZc = bits.length ∧ Ran a b (g.nats.flatMap natWord).length [] grpT tblM ∧
        Cst b ∧ C.inp.drop b.ip = vs.flatMap natWord ++ rest) := by
  set N := g.rows.length with hN
  have hsub : ∀ k, ((g.rows.take k).flatMap (cntsOf bits)).sum ≤ (g.rows.flatMap (cntsOf bits)).sum := by
    intro k
    have e : g.rows.flatMap (cntsOf bits) = (g.rows.take k).flatMap (cntsOf bits) ++
        (g.rows.drop k).flatMap (cntsOf bits) := by rw [← List.flatMap_append, List.take_append_drop]
    rw [e, List.sum_append]; omega
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gTk = k ∧ b.env gTG = N ∧
    (0 < k → b.env gS = g.s ∧ b.env gAct = g.pat.sum % 2 ∧ b.env gDn = g.dl.length ∧
      b.ram sHd = g.dl.flatMap intNats ∧ b.rc sHd = 2 * g.dl.length ∧ b.rc sZc = bits.length) ∧
    (b.ram sHd).length ≤ 2 * g.dl.length ∧ b.rc sHd ≤ 2 * g.dl.length ∧ b.ram sZc = bits ∧
    b.rc sZc ≤ bits.length ∧
    b.ram sI = ovw oI ((g.rows.take k).flatMap rowI) ∧ b.rc sI = ((g.rows.take k).flatMap rowI).length ∧
    b.ram sC = ovw oC ((g.rows.take k).flatMap (cntsOf bits)) ∧
    b.rc sC = ((g.rows.take k).flatMap (cntsOf bits)).length ∧
    b.env gSum = ((g.rows.take k).flatMap (cntsOf bits)).sum ∧
    Ran a b (((g.rows.take k).flatMap fun r => tblNats (g.tbl r)).flatMap natWord).length [] grpT tblM ∧ Cst b ∧
    C.inp.drop b.ip = ((g.rows.drop k).flatMap (fun r => tblNats (g.tbl r)) ++ vs).flatMap natWord ++ rest
  have loop := loopCnt (C := C) gTk gTG (by decide) (.seq tableS (.op (.inc gTk))) N
    (tblCostU ℓ g.pat.length g.dl.length bits.length + 2) I (fun k b hb => ⟨hb.1, hb.2.1⟩) (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      have hk' : g.rows.drop k = g.rows[k] :: g.rows.drop (k + 1) := List.drop_eq_getElem_cons hk
      have hmem : g.rows[k] ∈ g.rows := List.getElem_mem hk
      have hin1 : C.inp.drop b.ip = (tblNats (g.tbl g.rows[k]) ++ ((g.rows.drop (k + 1)).flatMap
          (fun r => tblNats (g.tbl r)) ++ vs)).flatMap natWord ++ rest := by
        rw [h15, hk', List.flatMap_cons, List.append_assoc]
      have hvk : ∀ v ∈ tblNats (g.tbl g.rows[k]), natBitLength v ≤ ℓ := fun v h =>
        hv v (List.mem_flatMap.mpr ⟨g.rows[k], hmem, h⟩)
      have hck : ((g.rows.take k).flatMap (cntsOf bits)).sum + (cnts g.rows[k].2.2.2 bits).sum < 2 ^ C.Wd := by
        have := hsub (k + 1)
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton, List.sum_append] at this
        have e : cntsOf bits g.rows[k] = cnts g.rows[k].2.2.2 bits := rfl
        rw [e] at this; omega
      refine (Hs.seq (t1 := tblCostU ℓ g.pat.length g.dl.length bits.length) (t2 := 1)
        ((tableS_spec b h14 (g.tbl g.rows[k]) bits _ rest hin1 h6 (hbl _ hmem).symm (by simpa [GrpD.tbl] using h4)
          oI ((g.rows.take k).flatMap rowI) h8 h9 oC ((g.rows.take k).flatMap (cntsOf bits)) h10 h11 _ h12 ℓ hvk hℓ
          hck hpat hdl).mono (by
            unfold tableCost tblCostU
            simp only [GrpD.tbl]
            rw [hbl _ hmem]
            omega) (fun _ h => h))
        (fun d ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ => ?_)).mono (by omega)
        (fun _ h => h)
      have dK : d.env gTk = k := by rw [e13.fr gTk (by decide), h1]
      refine Hs.mono (hs_inc C gTk d (by rw [dK]; omega)) le_rfl ?_
      rintro f rfl
      have tI : (g.rows.take (k + 1)).flatMap rowI = (g.rows.take k).flatMap rowI ++
          [g.rows[k].1, g.rows[k].2.1.natAbs, g.rows[k].2.2.1.natAbs] := by
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton]; rfl
      have tC : (g.rows.take (k + 1)).flatMap (cntsOf bits) = (g.rows.take k).flatMap (cntsOf bits) ++
          cnts g.rows[k].2.2.2 bits := by
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton]; rfl
      refine ⟨by rw [DS.set_env_self, dK], ?_, fun _ => ⟨?_, ?_, ?_, e5, e6, e12⟩, ?_, ?_, e11, by rw [DS.set_rc, e12],
        by rw [DS.set_ram, e7, tI]; rfl, ?_, by rw [DS.set_ram, e9, tC]; rfl, ?_, ?_, ?_, ?_, by rw [DS.set_ip]; exact e15⟩
      · rw [DS.set_env_ne _ _ (show gTG ≠ gTk by decide), e13.fr gTG (by decide), h2]
      · rw [DS.set_env_ne _ _ (show gS ≠ gTk by decide), e1]; rfl
      · rw [DS.set_env_ne _ _ (show gAct ≠ gTk by decide), e2]; rfl
      · rw [DS.set_env_ne _ _ (show gDn ≠ gTk by decide), e3]; rfl
      · rw [DS.set_ram, e5, intNats_flatMap_length]; rfl
      · rw [DS.set_rc, e6]; rfl
      · rw [DS.set_rc, e8, tI]; simp
      · rw [DS.set_rc, e10, tC]; simp; rfl
      · rw [DS.set_env_ne _ _ (show gSum ≠ gTk by decide), e4, tC, List.sum_append]; rfl
      · have hr := (h13.trans (e13.weaken (fun y hy => List.mem_cons_of_mem _ hy) (fun _ h => h))).set
          (x := gTk) (d.env gTk + 1) List.mem_cons_self
        refine hr.eqk ?_ (by simp)
        rw [List.take_succ_eq_append_getElem hk, List.flatMap_append, List.flatMap_singleton, List.flatMap_append,
          List.length_append]
      · exact cst_set e14 _ (by decide))
  refine Hx.hs (Hs.then (hs_zero C gTk a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨by vsimp [], by rw [DS.set_env_ne _ _ (show gTG ≠ gTk by decide), hTG],
    fun h => absurd h (lt_irrefl 0), hHd, hHdc, hZ, hZc, by simp [ovw_nil, hI], by simp [hIc],
    by simp [ovw_nil, hCr], by simp [hCc], by vsimp [hσ],
    ((Ran.refl a grpT tblM).set 0 (by decide)).eqk (by simp) rfl, cst_set hc _ (by decide),
    by rw [DS.set_ip, List.drop_zero]; exact hin⟩)
    (fun b ⟨_, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ n hn => ?_)
  have hpos : 0 < N := List.length_pos_iff.mpr hne
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := h3 hpos
  rw [List.take_length] at h8 h9 h10 h11 h12 h13
  rw [List.drop_length] at h15
  have e : N * (tblCostU ℓ g.pat.length g.dl.length bits.length + 2 + 2) =
    N * (tblCostU ℓ g.pat.length g.dl.length bits.length + 4) := by ring
  refine ⟨⟨q1, q2, q3, h2, h12, q4, q5, h8, h9, h10, h11, h6, q6, h13, h14, by simpa using h15⟩, by omega⟩

end NearQuarticWires.Reconstruct.GatherProg
