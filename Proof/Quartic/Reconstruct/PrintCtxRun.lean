import Proof.Quartic.Reconstruct.PrintCtx

/-!
# The context writer

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`ctxWriteS` writes `marksD 2 (ctxWordOf …) ++ bitD 1 false`, the framed context at depth `1`, from the fields held in
variables and in the stores `sF` (rates) and `sZ` (certified bits) (`ctxWriteS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearCubicWires.RepairOrdinary (frame)

variable {C : Ctx}

/-- The context word from its fields. -/
def ctxWordOf (n M A L J pb B0 B1 nc tg : ℕ) (fs : List ℕ) (bits : List Bool) : List Bool :=
  natWord n ++ natWord M ++ natWord A ++ natWord L ++ natWord J ++ listWord natWord fs ++ natWord pb ++ natWord B0 ++
    natWord B1 ++ natWord nc ++ natWord tg ++ listWord bitWord bits

/-- Write the context. -/
def ctxWriteS : St VV MM := (.seq (emitV kN 2) (.seq (emitV kM 2) (.seq (emitV kA 2) (.seq (emitV kL 2) (.seq (emitV kJ 2) (.seq (emitV kJ 2) (.seq (emitStoreS sF kI kJ (emitNatD 2)) (.seq (emitV kPair 2) (.seq (emitV kB0 2) (.seq (emitV kB1 2) (.seq (emitV kC 2) (.seq (emitV kG 2) (.seq (emitV kC 2) (.seq (bitsS) (putD 1 false)))))))))))))))

/-- The cost of `ctxWriteS`. -/
def ctxCost (ℓ J nc : ℕ) : ℕ :=
  13 * (emitNatDCost 2 ℓ + 2) + (J + J * (emitNatDCost 2 ℓ + 6) + 6) + (2 * nc + 1 + nc * (emitNatDCost 2 1 + 8) + 6) +
    25

theorem bitWord_eq_natWord (b : Bool) : bitWord b = natWord b.toNat := by cases b <;> rfl

theorem putD_step {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w ctxT) (hc : Cst b) :
    Hs C (putD 1 false) b 5 (fun c => OutMoved a c (w ++ bitD 1 false) ctxT ∧ Cst c) := by
  refine (putD_spec 1 false b).mono (by norm_num) (fun _ hw => ⟨acc.trans ((OutMoved.of_wrote hw acc.rcok).weaken
    (by decide)), hw.cst hc (by decide)⟩)

theorem bitsS_step {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w ctxT) (hc : Cst b) {bits : List Bool}
    (hz : b.ram sZ = (frame bits).map Bool.toNat) (hn : b.env kC = bits.length) (hN : bits.length < 2 ^ C.Wd)
    (hW : 3 ≤ C.Wd) :
    Hs C bitsS b (b.rc sZ + 1 + (bits.length * (emitNatDCost 2 1 + 4 + 4) + 4) + 1)
      (fun c => OutMoved a c (w ++ bits.flatMap fun x => marksD 2 (natWord x.toNat)) ctxT ∧ Cst c) :=
  (bitsS_spec b hc acc.rcok bits hz hn hN hW).mono le_rfl (fun _ ⟨m, cc⟩ => ⟨acc.trans m, cc⟩)

theorem emitStoreS_step {a b : DS VV MM} {w : List Bool} (acc : OutMoved a b w ctxT) (hc : Cst b) {fs : List ℕ}
    (hfs : b.ram sF = fs) (hn : b.env kJ = fs.length) (hN : fs.length < 2 ^ C.Wd) (ℓ : ℕ)
    (hℓ : ∀ v ∈ fs, natBitLength v ≤ ℓ) (hW : ℓ + 3 ≤ C.Wd) :
    Hs C (emitStoreS sF kI kJ (emitNatD 2)) b (b.rc sF + 1 + (fs.length * (emitNatDCost 2 ℓ + 1 + 1 + 4) + 4) + 1)
      (fun c => OutMoved a c (w ++ fs.flatMap fun v => marksD 2 (natWord v)) ctxT ∧ Cst c) := by
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  refine (emitStoreS_spec sF kI kJ (emitNatD 2) (fun v => marksD 2 (natWord v)) emitNatDT (emitNatDCost 2 ℓ)
    (by decide) (by decide) (by decide) fs (fun c cc cok hm => ?_) b hc acc.rcok hfs hn hN).mono le_rfl
    (fun c ⟨m, cc⟩ => ⟨acc.trans (m.weaken (by decide)), cc⟩)
  have hv := hℓ _ hm
  refine (emitNatD_spec 2 c cc (by omega) (by omega)).mono (emitNatDCost_mono 2 hv) (fun d ⟨wd, cd⟩ =>
    ⟨OutMoved.of_wrote wd cok, by rw [wd.rc], cd⟩)

/-- **Writing the context.** -/
theorem ctxWriteS_spec (a : DS VV MM) (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length)
    (n M A L J pb B0 B1 nc tg : ℕ) (fs : List ℕ) (bits : List Bool) (hn : a.env kN = n) (hM : a.env kM = M)
    (hA : a.env kA = A) (hL : a.env kL = L) (hJ : a.env kJ = J) (hpb : a.env kPair = pb) (hB0 : a.env kB0 = B0)
    (hB1 : a.env kB1 = B1) (hnc : a.env kC = nc) (htg : a.env kG = tg) (hfs : a.ram sF = fs) (hfl : fs.length = J)
    (hz : a.ram sZ = (frame bits).map Bool.toNat) (hbl : bits.length = nc) (ℓ : ℕ)
    (hℓ : ∀ v ∈ [n, M, A, L, J, pb, B0, B1, nc, tg] ++ fs, natBitLength v ≤ ℓ) (hW : ℓ + 3 ≤ C.Wd) :
    Hs C ctxWriteS a (ctxCost ℓ J nc)
      (fun b => OutMoved a b (marksD 2 (ctxWordOf n M A L J pb B0 B1 nc tg fs bits) ++ bitD 1 false) ctxT ∧ Cst b) := by
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have bw : ∀ v, v ∈ [n, M, A, L, J, pb, B0, B1, nc, tg] → natBitLength v + 2 < 2 ^ C.Wd := fun v hv => by
    have := hℓ v (by simp only [List.mem_append]; exact Or.inl hv); omega
  have hbl' : ∀ v, v ∈ [n, M, A, L, J, pb, B0, B1, nc, tg] → v < 2 ^ C.Wd := fun v hv => by
    have h1 := hℓ v (by simp only [List.mem_append]; exact Or.inl hv)
    have h2 := lt_natBitLength v
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have acc0 : OutMoved a a [] ctxT := OutMoved.refl a ctxT hok
  unfold ctxWriteS
  refine Hx.hs (Hs.then (emitV_step kN (by decide) acc0 hc n (by rw [acc0.fr kN (by decide), hn]) (by omega) (bw n (by simp))) (fun b1 ⟨acc1, c1⟩ n1 hn1 => ?_))
  refine Hs.then (emitV_step kM (by decide) acc1 c1 M (by rw [acc1.fr kM (by decide), hM]) (by omega) (bw M (by simp))) (fun b2 ⟨acc2, c2⟩ n2 hn2 => ?_)
  refine Hs.then (emitV_step kA (by decide) acc2 c2 A (by rw [acc2.fr kA (by decide), hA]) (by omega) (bw A (by simp))) (fun b3 ⟨acc3, c3⟩ n3 hn3 => ?_)
  refine Hs.then (emitV_step kL (by decide) acc3 c3 L (by rw [acc3.fr kL (by decide), hL]) (by omega) (bw L (by simp))) (fun b4 ⟨acc4, c4⟩ n4 hn4 => ?_)
  refine Hs.then (emitV_step kJ (by decide) acc4 c4 J (by rw [acc4.fr kJ (by decide), hJ]) (by omega) (bw J (by simp))) (fun b5 ⟨acc5, c5⟩ n5 hn5 => ?_)
  refine Hs.then (emitV_step kJ (by decide) acc5 c5 J (by rw [acc5.fr kJ (by decide), hJ]) (by omega) (bw J (by simp))) (fun b6 ⟨acc6, c6⟩ n6 hn6 => ?_)
  refine Hs.then (emitStoreS_step (fs := fs) acc6 c6 (by rw [acc6.ram, hfs]) (by rw [acc6.fr kJ (by decide), hJ, hfl]) (by rw [hfl]; exact hbl' J (by simp)) ℓ (fun v hv => hℓ v (by simp [hv])) (by omega)) (fun b7 ⟨acc7, c7⟩ n7 hn7 => ?_)
  refine Hs.then (emitV_step kPair (by decide) acc7 c7 pb (by rw [acc7.fr kPair (by decide), hpb]) (by omega) (bw pb (by simp))) (fun b8 ⟨acc8, c8⟩ n8 hn8 => ?_)
  refine Hs.then (emitV_step kB0 (by decide) acc8 c8 B0 (by rw [acc8.fr kB0 (by decide), hB0]) (by omega) (bw B0 (by simp))) (fun b9 ⟨acc9, c9⟩ n9 hn9 => ?_)
  refine Hs.then (emitV_step kB1 (by decide) acc9 c9 B1 (by rw [acc9.fr kB1 (by decide), hB1]) (by omega) (bw B1 (by simp))) (fun b10 ⟨acc10, c10⟩ n10 hn10 => ?_)
  refine Hs.then (emitV_step kC (by decide) acc10 c10 nc (by rw [acc10.fr kC (by decide), hnc]) (by omega) (bw nc (by simp))) (fun b11 ⟨acc11, c11⟩ n11 hn11 => ?_)
  refine Hs.then (emitV_step kG (by decide) acc11 c11 tg (by rw [acc11.fr kG (by decide), htg]) (by omega) (bw tg (by simp))) (fun b12 ⟨acc12, c12⟩ n12 hn12 => ?_)
  refine Hs.then (emitV_step kC (by decide) acc12 c12 nc (by rw [acc12.fr kC (by decide), hnc]) (by omega) (bw nc (by simp))) (fun b13 ⟨acc13, c13⟩ n13 hn13 => ?_)
  refine Hs.then (bitsS_step (bits := bits) acc13 c13 (by rw [acc13.ram, hz]) (by rw [acc13.fr kC (by decide), hnc, hbl]) (by rw [hbl]; exact hbl' nc (by simp)) (by omega)) (fun b14 ⟨acc14, c14⟩ n14 hn14 => ?_)
  refine Hs.last (putD_step acc14 c14) (fun b15 ⟨acc15, c15⟩ n15 hn15 => ⟨⟨?_, c15⟩, ?_⟩)
  · have heq : [] ++ marksD 2 (natWord n) ++ marksD 2 (natWord M) ++ marksD 2 (natWord A) ++ marksD 2 (natWord L) ++
        marksD 2 (natWord J) ++ marksD 2 (natWord J) ++ fs.flatMap (fun v => marksD 2 (natWord v)) ++
        marksD 2 (natWord pb) ++ marksD 2 (natWord B0) ++ marksD 2 (natWord B1) ++ marksD 2 (natWord nc) ++
        marksD 2 (natWord tg) ++ marksD 2 (natWord nc) ++ bits.flatMap (fun x => marksD 2 (natWord x.toNat)) ++
        bitD 1 false = marksD 2 (ctxWordOf n M A L J pb B0 B1 nc tg fs bits) ++ bitD 1 false := by
      unfold ctxWordOf listWord
      simp only [marksD_append, marksD_flatMap, bitWord_eq_natWord, hfl, hbl, List.nil_append, List.append_assoc]
    rw [← heq]; exact acc15
  · have e : ∀ v ∈ [n, M, A, L, J, pb, B0, B1, nc, tg], emitNatDCost 2 (natBitLength v) ≤ emitNatDCost 2 ℓ :=
      fun v hv => emitNatDCost_mono 2 (hℓ v (by simp only [List.mem_append]; exact Or.inl hv))
    have r6 : b6.rc sF ≤ J := by have := acc6.rcok sF; rw [acc6.ram, hfs, hfl] at this; exact this
    have r13 : b13.rc sZ ≤ 2 * nc + 1 := by
      have := acc13.rcok sZ; rw [acc13.ram, hz, frame_map_length, hbl] at this; exact this
    have e1 := e n (by simp)
    have e2 := e M (by simp)
    have e3 := e A (by simp)
    have e4 := e L (by simp)
    have e5 := e J (by simp)
    have e8 := e pb (by simp)
    have e9 := e B0 (by simp)
    have e10 := e B1 (by simp)
    have e11 := e nc (by simp)
    have e12 := e tg (by simp)
    rw [hfl] at hn7
    rw [hbl] at hn14
    unfold ctxCost
    have h5 : 5 ≤ emitNatDCost 2 ℓ + 2 := by unfold emitNatDCost; omega
    have q1 : J * (emitNatDCost 2 ℓ + 1 + 1 + 4) = J * (emitNatDCost 2 ℓ + 6) := by ring
    have q2 : nc * (emitNatDCost 2 1 + 4 + 4) = nc * (emitNatDCost 2 1 + 8) := by ring
    omega

end NearQuarticWires.Reconstruct
