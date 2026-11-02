import Proof.Quartic.Reconstruct.PrintDig

/-!
# Writing the index of a printed table

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; the index word is `Greedy.printIndexWord`.

`printIdxS` writes, at depth `2`, the index of one table from the counters of the enumeration: the bit of the part, the
eight bits of the pattern counter, the prime, the digits of the two digit-vector counters (shifted by `h_E - 1`), and
the two residues (`idxS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The constant `8`. -/
def q8 : Fin VV := ⟨24, by decide⟩
/-- The constant `128`. -/
def q128 : Fin VV := ⟨25, by decide⟩
/-- The pattern counter. -/
def qSig : Fin VV := ⟨26, by decide⟩
/-- The bit of the part. -/
def qSb : Fin VV := ⟨27, by decide⟩
/-- The prime. -/
def qP : Fin VV := ⟨28, by decide⟩
/-- The number `2(J+1)` of digits. -/
def qLen : Fin VV := ⟨29, by decide⟩
/-- The power `B^J` of the digit base. -/
def qTop : Fin VV := ⟨30, by decide⟩
/-- The digit base `B = 2h_E - 1`. -/
def qBase : Fin VV := ⟨31, by decide⟩
/-- The number `J + 1` of digits of a circuit. -/
def qJp1 : Fin VV := ⟨32, by decide⟩
/-- The digit counter of the first circuit. -/
def qX0 : Fin VV := ⟨33, by decide⟩
/-- The digit counter of the second circuit. -/
def qX1 : Fin VV := ⟨34, by decide⟩
/-- The digit shift of the first circuit. -/
def qO0 : Fin VV := ⟨35, by decide⟩
/-- The digit shift of the second circuit. -/
def qO1 : Fin VV := ⟨36, by decide⟩
/-- The first residue. -/
def qR0 : Fin VV := ⟨37, by decide⟩
/-- The second residue. -/
def qR1 : Fin VV := ⟨38, by decide⟩

/-- Write the index of one table at depth `2`. -/
def printIdxS : St VV MM :=
  .seq (emitV qSb 2) (.seq (emitV q8 2) (.seq (.op (.copy qPw q128)) (.seq (digLoopS qSig v2 q8 (emitV qDg 2))
  (.seq (emitV qP 2) (.seq (emitV qLen 2) (.seq (.op (.copy qPw qTop)) (.seq (digLoopS qX0 qBase qJp1 (emitShiftD 2 qDg qO0))
  (.seq (.op (.copy qPw qTop)) (.seq (digLoopS qX1 qBase qJp1 (emitShiftD 2 qDg qO1)) (.seq (emitV v2 2)
  (.seq (emitShiftD 2 qR0 vZ) (emitShiftD 2 qR1 vZ))))))))))))

/-- The variables written by `printIdxS`. -/
def printIdxT : List (Fin VV) := digT ++ emitVT

/-- The word written by `printIdxS`. -/
def printIdxW (sb is p len B J1 x0 x1 o0 o1 y0 y1 : ℕ) : List Bool :=
  marksD 2 (natWord sb) ++ marksD 2 (natWord 8) ++
    (List.range 8).flatMap (fun j => marksD 2 (natWord ((is / 2 ^ (8 - 1 - j)) % 2))) ++ marksD 2 (natWord p) ++
    marksD 2 (natWord len) ++
    (List.range J1).flatMap (fun j => marksD 2 (NearCubicGates.Close.Interfaces.intWord
      ((((x0 / B ^ (J1 - 1 - j)) % B : ℕ) : ℤ) - (o0 : ℤ)))) ++
    (List.range J1).flatMap (fun j => marksD 2 (NearCubicGates.Close.Interfaces.intWord
      ((((x1 / B ^ (J1 - 1 - j)) % B : ℕ) : ℤ) - (o1 : ℤ)))) ++
    marksD 2 (natWord 2) ++ marksD 2 (NearCubicGates.Close.Interfaces.intWord ((y0 : ℤ) - (0 : ℕ))) ++
    marksD 2 (NearCubicGates.Close.Interfaces.intWord ((y1 : ℤ) - (0 : ℕ)))

theorem emitV_rc (x : Fin VV) (hx : x ≠ t3) (d : ℕ) (a : DS VV MM) (hc : Cst a)
    (hok : ∀ m, a.rc m ≤ (a.ram m).length) (hW : 2 ≤ C.Wd) (hv : natBitLength (a.env x) + 2 < 2 ^ C.Wd) :
    Hs C (emitV x d) a (emitNatDCost d (natBitLength (a.env x)) + 2)
      (fun b => OutMoved a b (marksD d (natWord (a.env x))) emitVT ∧ b.rc = a.rc ∧ Cst b) := by
  refine Hx.hs (Hs.then (hs_copy C t3 x a (Ne.symm hx)) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have c0 : Cst (a.set t3 (a.env x)) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  refine Hs.last (emitNatD_spec d _ c0 hW (by rw [DS.set_env_self]; exact hv)) (fun b ⟨w1, c1⟩ n hn => ⟨⟨?_, ?_, c1⟩, ?_⟩)
  · rw [DS.set_env_self] at w1
    exact ⟨by rw [w1.out, DS.set_out], by rw [w1.ip, DS.set_ip], by rw [w1.ram, DS.set_ram],
      by rw [w1.kin, DS.set_kin], by rw [w1.kout, DS.set_kout], by rw [w1.kc, DS.set_kc],
      Fr.trans (Fr.set a _ List.mem_cons_self) (w1.fr.weaken (fun y hy => List.mem_cons_of_mem _ hy)),
      fun m => by rw [w1.rc, w1.ram, DS.set_rc, DS.set_ram]; exact hok m⟩
  · rw [w1.rc, DS.set_rc]
  · rw [DS.set_env_self] at hn; omega

theorem emitShift_rc (x B : Fin VV) (hxB : x ≠ B) (hx : x ∉ emitShiftT) (hB : B ∉ emitShiftT) (a : DS VV MM)
    (hc : Cst a) (hok : ∀ m, a.rc m ≤ (a.ram m).length) (hW : 2 ≤ C.Wd)
    (hv : natBitLength (a.env x + a.env B) + 2 < 2 ^ C.Wd) :
    Hs C (emitShiftD 2 x B) a (emitShiftCost 2 (natBitLength (a.env x + a.env B)))
      (fun b => OutMoved a b (marksD 2 (NearCubicGates.Close.Interfaces.intWord ((a.env x : ℤ) - a.env B))) emitVT ∧
        b.rc = a.rc ∧ Cst b) :=
  (emitShiftD_spec 2 x B hxB hx hB a hc hW hv).mono le_rfl (fun _ ⟨w, cb⟩ =>
    ⟨(OutMoved.of_wrote w hok).weaken (fun _ hy => hy), w.rc, cb⟩)

end NearQuarticWires.Reconstruct
