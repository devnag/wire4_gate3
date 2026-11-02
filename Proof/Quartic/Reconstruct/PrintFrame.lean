import Proof.Quartic.Reconstruct.PrintBasic

/-!
# Copying a framed word into a record store

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`rawFrameS m` reads a framed word `frame u` (pairs `true, b` and the end mark `false`) and appends its bits, as
`0`/`1`, to store `m` (`rawFrameS_spec`). The printing stage uses it for the certified bits, the prefix of the seed
path (into a scratch store) and the coefficient table.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {C : Ctx}

/-- Copy the framed word at the input into store `m`, marks included. -/
def rawFrameS (m : Fin MM) : St VV MM :=
  .seq (.op (.zero fE)) (.loop (.lt fE v1) (.seq (.op (.rdI fM)) (.seq (.op (.wrM m fM))
    (.ite (.eq fM v1) (.seq (.op (.rdI fB)) (.op (.wrM m fB))) (.op (.inc fE))))))

/-- The variables written by `rawFrameS`. -/
def rawFrameT : List (Fin VV) := [fE, fM, fB]

theorem marks_take_succ (u : List Bool) (k : ℕ) (hk : k < u.length) :
    marks (u.take (k + 1)) = marks (u.take k) ++ [true, u[k]] := by
  rw [marks_eq_flatMap, marks_eq_flatMap, List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp

/-- **Copying a framed word.** -/
theorem rawFrameS_spec (m : Fin MM) (a : DS VV MM) (hc : Cst a) (u rest : List Bool)
    (hin : C.inp.drop a.ip = frame u ++ rest) (hend : a.rc m = (a.ram m).length) (hW : 2 < 2 ^ C.Wd) :
    Hs C (rawFrameS m) a ((u.length + 1) * 10 + 4)
      (fun b => InMoved a b m (frame u).length ((frame u).map Bool.toNat) rawFrameT ∧
        C.inp.drop b.ip = rest ∧ Cst b) := by
  have hTc : vZ ∉ rawFrameT ∧ v1 ∉ rawFrameT ∧ v2 ∉ rawFrameT := by decide
  let P : ℕ → DS VV MM → Prop := fun k b => Cst b ∧ b.rc m = (b.ram m).length ∧
    (k ≤ u.length → b.env fE = 0 ∧ C.inp.drop b.ip = frame (u.drop k) ++ rest ∧
      InMoved a b m (2 * k) ((marks (u.take k)).map Bool.toNat) rawFrameT) ∧
    (u.length < k → b.env fE = 1 ∧ C.inp.drop b.ip = rest ∧
      InMoved a b m (frame u).length ((frame u).map Bool.toNat) rawFrameT)
  have loop : ∀ b, P 0 b → Hs C (.loop (.lt fE v1) (.seq (.op (.rdI fM)) (.seq (.op (.wrM m fM))
      (.ite (.eq fM v1) (.seq (.op (.rdI fB)) (.op (.wrM m fB))) (.op (.inc fE)))))) b
      ((u.length + 1) * (8 + 2) + 2) (P (u.length + 1)) := by
    refine Hs.loopN (c := .lt fE v1) (show fE ≠ v1 by decide) P (u.length + 1) 8 ?_ ?_
    · intro k hk b ⟨hcb, hendb, h1, _⟩
      obtain ⟨e0, ein, emv⟩ := h1 (by omega)
      refine ⟨by simp [Cnd.eval, e0, hcb.one], ?_⟩
      rcases Nat.lt_or_ge k u.length with hku | hku
      · -- a data bit
        have hd : u.drop k = u[k] :: u.drop (k + 1) := List.drop_eq_getElem_cons hku
        rw [hd, frame_cons'] at ein
        refine Hx.hs (Hs.then (rdI_spec' fM m b true _ ein) (fun b1 ⟨x1, d1, m1⟩ n1 hn1 => ?_))
        refine Hs.then (wrM_spec' m fM b1 (m1.endc hendb)) (fun b2 ⟨m2, v2⟩ n2 hn2 => ?_)
        have c2 : Cst b2 := ⟨by rw [v2]; exact (m1.cst hcb (by decide)).z, by rw [v2]; exact (m1.cst hcb (by decide)).one,
          by rw [v2]; exact (m1.cst hcb (by decide)).two⟩
        have hf2 : b2.env fM = 1 := by rw [v2, x1]; rfl
        have hbr : Hs C (.seq (.op (.rdI fB)) (.op (.wrM m fB))) b2 3 (P (k + 1)) := by
          refine Hx.hs (Hs.then (rdI_spec' fB m b2 u[k] (frame (u.drop (k + 1)) ++ rest)
            (by rw [m2.ip, Nat.add_zero, d1]; rfl)) (fun b3 ⟨x3, d3, m3⟩ n3 hn3 => ?_))
          refine Hs.last (wrM_spec' m fB b3 (m3.endc (m2.endc (m1.endc hendb)))) (fun b4 ⟨m4, v4⟩ n4 hn4 => ⟨?_, ?_⟩)
          · have mv := (((emv.trans (m1.weaken (by decide))).trans (m2.weaken (by decide))).trans
              (m3.weaken (by decide))).trans (m4.weaken (by decide))
            have c3 := m3.cst c2 (by decide)
            have c4 : Cst b4 := ⟨by rw [v4]; exact c3.z, by rw [v4]; exact c3.one, by rw [v4]; exact c3.two⟩
            refine ⟨c4, m4.endc (m3.endc (m2.endc (m1.endc hendb))), fun _ => ⟨?_, ?_, ?_⟩,
              fun h => absurd h (by omega)⟩
            · rw [v4, m3.fr fE (by decide), v2, m1.fr fE (by decide), e0]
            · rw [m4.ip, Nat.add_zero, d3]
            · rw [x1, x3] at mv
              rw [marks_take_succ u k hku, List.map_append]
              have e : 2 * k + 1 + 0 + 1 + 0 = 2 * (k + 1) := by ring
              rw [e] at mv
              simpa using mv
          · omega
        refine Hs.last (Hs.iteT (show fM ≠ v1 by decide) (by simp [Cnd.eval, hf2, c2.one]) hbr)
          (fun b5 h5 n5 hn5 => ⟨h5, by omega⟩)
      · -- the end mark
        have hk' : k = u.length := by omega
        subst hk'
        rw [List.drop_length, frame_nil'] at ein
        refine Hx.hs (Hs.then (rdI_spec' fM m b false _ ein) (fun b1 ⟨x1, d1, m1⟩ n1 hn1 => ?_))
        refine Hs.then (wrM_spec' m fM b1 (m1.endc hendb)) (fun b2 ⟨m2, v2⟩ n2 hn2 => ?_)
        have c2 : Cst b2 := ⟨by rw [v2]; exact (m1.cst hcb (by decide)).z, by rw [v2]; exact (m1.cst hcb (by decide)).one,
          by rw [v2]; exact (m1.cst hcb (by decide)).two⟩
        have hf2 : b2.env fM = 0 := by rw [v2, x1]; rfl
        have hE2 : b2.env fE = 0 := by rw [v2, m1.fr fE (by decide), e0]
        refine Hs.last (Hs.iteF (show fM ≠ v1 by decide) (by simp [Cnd.eval, hf2, c2.one])
          (hs_inc C fE b2 (by rw [hE2]; omega))) (fun b3 hb3 n3 hn3 => ⟨?_, by omega⟩)
        subst hb3
        have mv := ((emv.trans (m1.weaken (by decide))).trans (m2.weaken (by decide))).set (b2.env fE + 1)
          (show fE ∈ rawFrameT by decide)
        rw [x1] at mv
        refine ⟨⟨by vsimp [c2.z], by vsimp [c2.one], by vsimp [c2.two]⟩, by
          simp only [DS.set_rc, DS.set_ram]; exact m2.endc (m1.endc hendb), fun h => absurd h (by omega),
          fun _ => ⟨by rw [DS.set_env_self, hE2], by simp only [DS.set_ip]; rw [m2.ip, Nat.add_zero, d1]; rfl, ?_⟩⟩
        rw [List.take_length] at mv
        have hf : (frame u).map Bool.toNat = (marks u).map Bool.toNat ++ [false.toNat] := by
          rw [frame_eq_marks, List.map_append]; rfl
        have hl : (frame u).length = 2 * u.length + 1 + 0 := by
          rw [frame_eq_marks, List.length_append, marks_eq_flatMap]; simp; ring
        rw [hf, hl]
        simpa using mv
    · intro b ⟨_, _, _, h2⟩
      have := (h2 (by omega)).1
      simp [Cnd.eval, this, ‹Cst b›.one]
  refine Hx.hs (Hs.then (hs_zero C fE a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩, by simpa using hend,
    fun _ => ⟨DS.set_env_self _ _ _, by simpa using hin, by simpa [marks_eq_flatMap] using (InMoved.refl a m rawFrameT).set 0 (by decide)⟩,
    fun h => absurd h (by omega)⟩) (fun b ⟨c, _, _, h2⟩ n hn => ⟨⟨(h2 (by omega)).2.2, (h2 (by omega)).2.1, c⟩, ?_⟩)
  omega

end NearQuarticWires.Reconstruct
