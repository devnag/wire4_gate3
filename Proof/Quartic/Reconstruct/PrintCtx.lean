import Proof.Quartic.Reconstruct.PrintCalc

/-!
# Writing the context

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The printing stage writes `frame (contextWord q)` as the first part of its output. This file has the writers it
uses: a number held in a variable (`emitV_step`) and the certified bits from their framed copy in store `sZ`
(`bitsS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- The variables written while writing the context. -/
def ctxT : List (Fin VV) := kI :: fM :: t3 :: emitNatDT

theorem emitV_step (x : Fin VV) (hx : x ∉ ctxT) {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w ctxT)
    (hcb : Cst b) (v : ℕ) (hv : b.env x = v) (hW : 2 ≤ C.Wd) (hvW : natBitLength v + 2 < 2 ^ C.Wd) :
    Hs C (emitV x 2) b (emitNatDCost 2 (natBitLength v) + 2)
      (fun c => OutMoved a c (w ++ marksD 2 (natWord v)) ctxT ∧ Cst c) := by
  have hxt : x ≠ t3 := fun h => hx (by rw [h]; decide)
  refine (emitV_spec x hxt 2 b hcb acc.rcok hW (by rw [hv]; exact hvW)).mono (by rw [hv]) ?_
  intro c ⟨m, cc⟩
  rw [hv] at m
  exact ⟨acc.trans (m.weaken (by decide)), cc⟩

theorem frame_map_getD (bits : List Bool) (k : ℕ) (hk : k < bits.length) :
    ((frame bits).map Bool.toNat).getD (2 * k) 0 = 1 ∧
      ((frame bits).map Bool.toNat).getD (2 * k + 1) 0 = (bits[k]).toNat := by
  induction bits generalizing k with
  | nil => simp at hk
  | cons b l ih =>
    rw [frame_cons']
    rcases k with _ | k
    · simp
    · have := ih k (by simpa using hk)
      simp only [List.map_cons, List.getElem_cons_succ] at this ⊢
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, show 2 * k + 2 + 1 = 2 * k + 1 + 2 by ring]
      simpa using this

theorem frame_map_length (bits : List Bool) : ((frame bits).map Bool.toNat).length = 2 * bits.length + 1 := by
  rw [List.length_map, RepairOrdinary.frame_length]

/-- Write the certified bits from their framed copy. -/
def bitsS : St VV MM :=
  .seq (.op (.rwM sZ)) (forS kI kC (.seq (.op (.rdM sZ fM)) (.seq (.op (.rdM sZ t3)) (emitNatD 2))))

theorem bool_getD_range_flatMap {α : Type} (bs : List Bool) (f : Bool → List α) :
    (List.range bs.length).flatMap (fun k => f (bs.getD k false)) = bs.flatMap f := by
  have : (List.range bs.length).map (fun k => bs.getD k false) = bs := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp [List.getElem?_eq_getElem (by simpa using h1)]
  conv_rhs => rw [← this]
  rw [List.flatMap_map]

/-- **Writing the certified bits.** -/
theorem bitsS_spec (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length) (bits : List Bool)
    (hz : a.ram sZ = (frame bits).map Bool.toNat) (hn : a.env kC = bits.length) (hN : bits.length < 2 ^ C.Wd)
    (hW : 3 ≤ C.Wd) :
    Hs C bitsS a (a.rc sZ + 1 + (bits.length * (emitNatDCost 2 1 + 4 + 4) + 4) + 1)
      (fun b => OutMoved a b (bits.flatMap fun x => marksD 2 (natWord x.toNat)) ctxT ∧ Cst b) := by
  have h8 : 8 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  refine Hx.hs (Hs.then (rwM_spec' sZ a hok ctxT) (fun b0 ⟨o0, r0, e0⟩ n0 hn0 => ?_))
  have c0 : Cst b0 := ⟨by rw [e0]; exact hc.z, by rw [e0]; exact hc.one, by rw [e0]; exact hc.two⟩
  let Inv : ℕ → DS VV MM → Prop := fun k b => Cst b ∧ b.rc sZ = 2 * k ∧ b.ram = a.ram ∧ b.ip = a.ip ∧
    b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b ctxT ∧ (∀ m, b.rc m ≤ (b.ram m).length)
  have hset : ∀ k b v, Inv k b → Inv k (b.set kI v) := fun k b v ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
    ⟨⟨by vsimp [h1.z], by vsimp [h1.one], by vsimp [h1.two]⟩, h2, h3, h4, h5, h6, h7,
      Fr.trans h8 (Fr.set b v (by decide)), h9⟩
  refine Hs.last (forS_spec kI kC (by decide) _ bits.length (emitNatDCost 2 1 + 4)
    (fun k => marksD 2 (natWord (bits.getD k false).toNat)) Inv hset ?_ b0
    ⟨c0, r0, o0.ram, o0.ip, o0.kin, o0.kout, o0.kc, o0.fr, o0.rcok⟩ (by rw [e0]; exact hn) hN)
    (fun b ⟨⟨b1, _, b3, b4, b5, b6, b7, b8, b9⟩, _, b10⟩ k hk => ⟨⟨⟨?_, b4, b3, b5, b6, b7, b8, b9⟩, b1⟩, by omega⟩)
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hik hnk
    obtain ⟨g1, g2⟩ := frame_map_getD bits k hk
    have hlen := frame_map_length bits
    have hl1 : b.rc sZ < (b.ram sZ).length := by rw [h2, h3, hz, hlen]; omega
    refine Hx.hs (Hs.then (rdM_spec' sZ fM b hl1 h9) (fun c1 ⟨x1, x2, x3⟩ n1 hn1 => ?_))
    have hl2 : c1.rc sZ < (c1.ram sZ).length := by rw [x2, x3.ram, h2, h3, hz, hlen]; omega
    refine Hs.then (rdM_spec' sZ t3 c1 hl2 x3.rcok) (fun c2 ⟨y1, y2, y3⟩ n2 hn2 => ?_)
    have v2 : c2.env t3 = (bits[k]).toNat := by rw [y1, x3.ram, x2, h2, h3, hz]; exact g2
    have cc2 : Cst c2 := y3.cst (x3.cst h1 (by decide)) (by decide)
    have hb1 : natBitLength (bits[k]).toNat ≤ 1 := by cases bits[k] <;> simp [natBitLength]
    refine Hs.last (emitNatD_spec 2 c2 cc2 (by omega) (by rw [v2]; omega)) (fun c3 ⟨w3, cc3⟩ n3 hn3 => ⟨?_, ?_⟩)
    · rw [v2] at w3
      refine ⟨⟨cc3, by rw [w3.rc, y2, x2, h2]; ring, by rw [w3.ram, y3.ram, x3.ram, h3], by rw [w3.ip, y3.ip, x3.ip, h4],
        by rw [w3.kin, y3.kin, x3.kin, h5], by rw [w3.kout, y3.kout, x3.kout, h6], by rw [w3.kc, y3.kc, x3.kc, h7],
        Fr.trans h8 (Fr.trans (x3.fr.weaken (by decide)) (Fr.trans (y3.fr.weaken (by decide)) (w3.fr.weaken
          (by decide)))), fun m => by rw [w3.rc, w3.ram]; exact y3.rcok m⟩,
        by rw [w3.fr kI (by decide), y3.fr kI (by decide), x3.fr kI (by decide), hik],
        by rw [w3.fr kC (by decide), y3.fr kC (by decide), x3.fr kC (by decide), hnk],
        by rw [w3.out, y3.out, x3.out, List.append_nil, List.append_nil, List.getD_eq_getElem _ _ hk]⟩
    · have : natBitLength (c2.env t3) = natBitLength (bits[k]).toNat := by rw [v2]
      have e1 : emitNatDCost 2 (natBitLength (c2.env t3)) ≤ emitNatDCost 2 1 := by
        rw [this]; exact emitNatDCost_mono 2 hb1
      omega
  · rw [b10, o0.out, List.append_nil, bool_getD_range_flatMap bits (fun x => marksD 2 (natWord x.toNat))]

end NearQuarticWires.Reconstruct
