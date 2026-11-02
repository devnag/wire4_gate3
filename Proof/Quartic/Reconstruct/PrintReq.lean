import Proof.Quartic.Reconstruct.PrintOut

/-!
# Writing one printed table request

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`reqS` writes one entry `frame (printIndexWord r) ++ frame (printInput r)` of the printing stage at depth `1`: the
index, the end mark, `prepWord`, the framed coefficient table, the index again and the end mark (`reqS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- Write one request at depth `1`. -/
def reqS : St VV MM :=
  .seq printIdxS (.seq (putD 1 false) (.seq (emitBitsS sP qj kPL) (.seq (emitFrameS sG) (.seq printIdxS (putD 1 false)))))

/-- The variables written by `reqS`. -/
def reqT : List (Fin VV) := printIdxT ++ [fE, fM, fB]

/-- The word of one request. -/
def reqWord (iw pw u : List Bool) : List Bool :=
  iw ++ bitD 1 false ++ marksD 2 pw ++ marksD 2 (frame u) ++ iw ++ bitD 1 false

/-- The cost of `reqS`. -/
def reqCost (ℓ J1 PL U : ℕ) : ℕ :=
  2 * printIdxCost ℓ J1 + (PL + 1 + (PL * 16 + 4) + 1) + (2 * U + 1 + 1 + (1 + ((U + 1) * 28 + 2) + 1) + 1) + 20

/-- **One request.** -/
theorem reqS_spec (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length)
    (sb is p len B J1 x0 x1 o0 o1 y0 y1 : ℕ) (h1 : a.env qSb = sb) (h2 : a.env q8 = 8) (h3 : a.env q128 = 128)
    (h4 : a.env qSig = is) (h5 : a.env qP = p) (h6 : a.env qLen = len) (h7 : a.env qTop = B ^ (J1 - 1))
    (h8 : a.env qBase = B) (h9 : a.env qJp1 = J1) (h10 : a.env qX0 = x0) (h11 : a.env qX1 = x1)
    (h12 : a.env qO0 = o0) (h13 : a.env qO1 = o1) (h14 : a.env qR0 = y0) (h15 : a.env qR1 = y1) (hB : 0 < B)
    (ℓ : ℕ) (hℓ : ∀ v ∈ [sb, 8, p, len, 2, B + o0, B + o1, y0, y1], natBitLength v ≤ ℓ) (hW : ℓ + 3 ≤ C.Wd)
    (hBW : 2 * B ^ J1 ≤ 2 ^ C.Wd) (hJW : J1 < 2 ^ C.Wd) (h512 : 512 ≤ 2 ^ C.Wd) (pw u : List Bool)
    (hP : a.ram sP = pw.map Bool.toNat) (hpl : a.env kPL = pw.length) (hPW : pw.length < 2 ^ C.Wd)
    (hG : a.ram sG = (frame u).map Bool.toNat) :
    Hs C reqS a (reqCost ℓ J1 pw.length u.length)
      (fun c => OutMoved a c (reqWord (printIdxW sb is p len B J1 x0 x1 o0 o1 y0 y1) pw u) reqT ∧ Cst c) := by
  have hT1 : ∀ y ∈ printIdxT, y ∈ reqT := fun y hy => List.mem_append_left _ hy
  refine Hx.hs (Hs.then (printIdxS_spec a hc hok sb is p len B J1 x0 x1 o0 o1 y0 y1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 h12 h13 h14 h15 hB ℓ hℓ hW hBW hJW h512) (fun b1 ⟨m1, c1⟩ n1 hn1 => ?_))
  have k1 : ∀ y, y ∉ printIdxT → b1.env y = a.env y := m1.fr
  refine Hs.then (putD_spec 1 false b1) (fun b2 w2 n2 hn2 => ?_)
  have m2 := OutMoved.of_wrote w2 m1.rcok
  have c2 : Cst b2 := w2.cst c1 (by decide)
  refine Hs.then (emitBitsS_spec sP qj kPL (by decide) (by decide) b2 c2 m2.rcok pw
    (by rw [m2.ram, m1.ram, hP]) (by rw [m2.fr kPL (by decide), k1 kPL (by decide), hpl]) hPW)
    (fun b3 ⟨m3, c3⟩ n3 hn3 => ?_)
  refine Hs.then (emitFrameS_spec sG b3 c3 m3.rcok u (by rw [m3.ram, m2.ram, m1.ram, hG]) (by omega))
    (fun b4 ⟨m4, c4⟩ n4 hn4 => ?_)
  have k4 : ∀ y, y ∉ reqT → b4.env y = a.env y := fun y hy => by
    rw [m4.fr y (fun h => hy (by simp at h ⊢; rcases h with h | h | h | h <;> subst h <;> decide)),
      m3.fr y (fun h => hy (by simp at h ⊢; rcases h with h | h | h <;> subst h <;> decide)),
      m2.fr y (fun h => hy (by simp at h ⊢; subst h; decide)), k1 y (fun h => hy (hT1 y h))]
  refine Hs.then (printIdxS_spec b4 c4 m4.rcok sb is p len B J1 x0 x1 o0 o1 y0 y1
    (by rw [k4 qSb (by decide), h1]) (by rw [k4 q8 (by decide), h2]) (by rw [k4 q128 (by decide), h3])
    (by rw [k4 qSig (by decide), h4]) (by rw [k4 qP (by decide), h5]) (by rw [k4 qLen (by decide), h6])
    (by rw [k4 qTop (by decide), h7]) (by rw [k4 qBase (by decide), h8]) (by rw [k4 qJp1 (by decide), h9])
    (by rw [k4 qX0 (by decide), h10]) (by rw [k4 qX1 (by decide), h11]) (by rw [k4 qO0 (by decide), h12])
    (by rw [k4 qO1 (by decide), h13]) (by rw [k4 qR0 (by decide), h14]) (by rw [k4 qR1 (by decide), h15])
    hB ℓ hℓ hW hBW hJW h512) (fun b5 ⟨m5, c5⟩ n5 hn5 => ?_)
  refine Hs.last (putD_spec 1 false b5) (fun b6 w6 n6 hn6 => ⟨⟨?_, w6.cst c5 (by decide)⟩, ?_⟩)
  · have m6 := OutMoved.of_wrote w6 m5.rcok
    have := ((((m1.weaken hT1).trans (m2.weaken (by decide))).trans (m3.weaken (by decide))).trans
      (m4.weaken (by decide))).trans ((m5.weaken hT1).trans (m6.weaken (by decide)))
    unfold reqWord
    simpa [List.append_assoc] using this
  · have r3 : b2.rc sP ≤ pw.length := by
      have := m2.rcok sP; rw [m2.ram, m1.ram, hP, List.length_map] at this; exact this
    have r4 : b3.rc sG ≤ 2 * u.length + 1 := by
      have := m3.rcok sG; rw [m3.ram, m2.ram, m1.ram, hG, frame_map_length] at this; exact this
    have p2 : 2 * 2 ^ 1 + 1 = 5 := by norm_num
    rw [p2] at hn2 hn6
    have q1 : pw.length * (2 * 2 ^ 2 + 2 + 1 + 1 + 4) = pw.length * 16 := by norm_num
    rw [q1] at hn3
    unfold reqCost
    omega

end NearQuarticWires.Reconstruct
