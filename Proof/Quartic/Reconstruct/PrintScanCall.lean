import Proof.Quartic.Reconstruct.PrintList

/-!
# Reading the tag and the call, counting

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `prop:time`.

`scanCallS` reads the tag of a dispatched call and the call word, counting its bits from zero
(`scanCallS_spec`): it keeps the arity `n` in `kN` and the kind tag in `kKd`, and reads past the two circuits, the
parity list and the radius with the counting scanners of `CallSkip`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord callWord kindTag circuitWord ratWord Call)
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx}

/-- The context: the kind tag of the call. -/
def kKd : Fin VV := ⟨88, by decide⟩

/-- Read the tag and the call word, counting from zero. -/
def scanCallS : St VV MM :=
  .seq (.op (.zero lengthCounter)) (.seq (.op (.rdI t0)) (.seq (.op (.inc lengthCounter))
    (.seq (scanVars [kN, kKd]) (.seq skipCircuit (.seq skipCircuit (.seq skipNatList skipRat))))))

/-- The variables written by `scanCallS`. -/
def scanCallT : List (Fin VV) := [kN, kKd] ++ gateListScratch

/-- The cost of `scanCallS` for a call word of `L` bits. -/
def scanCallCost (L : ℕ) : ℕ := 3000 * (L + 1) ^ 3 + 100

theorem atom_in_gate : ∀ y ∈ atomScratch, y ∈ gateListScratch := by decide
theorem scalar_in_gate : ∀ y ∈ scalarListScratch, y ∈ gateListScratch := by decide

/-- **Reading the tag and the call.** -/
theorem scanCallS_spec (a : DS VV MM) (hc : Cst a) (c : Call) (rest : List Bool)
    (hin : C.inp.drop a.ip = true :: (callWord c ++ rest)) (hW : (callWord c).length + 4 ≤ C.Wd) :
    Hs C scanCallS a (scanCallCost (callWord c).length)
      (fun b => b.env kN = c.n ∧ b.env kKd = kindTag c.kind ∧ b.env lengthCounter = 1 + (callWord c).length ∧
        b.ip = a.ip + (1 + (callWord c).length) ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b (t0 :: scanCallT) ∧ Cst b ∧
        C.inp.drop b.ip = rest) := by
  set L := (callWord c).length with hL
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hWL : L < 2 ^ C.Wd := by omega
  have hcw : callWord c = [c.n, kindTag c.kind].flatMap natWord ++ (circuitWord c.first ++ (circuitWord c.second ++
      (listWord natWord c.parity ++ ratWord c.radius))) := by
    simp [callWord, List.append_assoc]
  have hlen := congrArg List.length hcw
  simp only [List.length_append] at hlen
  refine Hx.hs (Hs.then (hs_zero C lengthCounter a) (fun a1 ha1 n1 hn1 => ?_))
  subst ha1
  obtain ⟨hb0, hl0⟩ := bitOf_drop hin
  refine Hs.then (hs_rdI C t0 _ (by simpa using hl0)) (fun a2 ha2 n2 hn2 => ?_)
  subst ha2
  have h2W : 2 ≤ 2 ^ C.Wd := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ C.Wd by omega))
  refine Hs.then (hs_inc C lengthCounter _ (by
    show ((a.set lengthCounter 0).set t0 (bitOf C.inp (a.set lengthCounter 0).ip)).env lengthCounter + 1 < 2 ^ C.Wd
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_self]; omega)) (fun a3 ha3 n3 hn3 => ?_)
  subst ha3
  set a3 := ({ (a.set lengthCounter 0).set t0 (bitOf C.inp (a.set lengthCounter 0).ip) with
    ip := (a.set lengthCounter 0).ip + 1 } : DS VV MM).set lengthCounter
    (({ (a.set lengthCounter 0).set t0 (bitOf C.inp (a.set lengthCounter 0).ip) with
    ip := (a.set lengthCounter 0).ip + 1 } : DS VV MM).env lengthCounter + 1) with ha3d
  have ip3 : a3.ip = a.ip + 1 := by rw [ha3d]; rfl
  have lc3 : a3.env lengthCounter = 1 := by
    rw [ha3d, DS.set_env_self]
    show ((a.set lengthCounter 0).set t0 (bitOf C.inp (a.set lengthCounter 0).ip)).env lengthCounter + 1 = 1
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_self]
  have fr3' : Fr a a3 [lengthCounter, t0] := by
    intro y hy
    have h1 : y ≠ lengthCounter := fun h => hy (by rw [h]; decide)
    have h2 : y ≠ t0 := fun h => hy (by rw [h]; decide)
    rw [ha3d, DS.set_env_ne _ _ h1]
    show ((a.set lengthCounter 0).set t0 (bitOf C.inp (a.set lengthCounter 0).ip)).env y = a.env y
    rw [DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
  have c3 : Cst a3 := Cst.of_fr hc fr3' (by decide)
  have hin3 : C.inp.drop a3.ip = callWord c ++ rest := by rw [ip3]; exact drop_succ_of_drop hin
  rw [hcw] at hin3
  have hin3' : C.inp.drop a3.ip = [c.n, kindTag c.kind].flatMap natWord ++ (circuitWord c.first ++
      (circuitWord c.second ++ (listWord natWord c.parity ++ (ratWord c.radius ++ rest)))) := by
    rw [hin3]; simp [List.append_assoc]
  have hvb : ∀ v ∈ [c.n, kindTag c.kind], natBitLength v ≤ L := by
    intro v hv
    have : (natWord v).length ≤ ([c.n, kindTag c.kind].flatMap natWord).length := by
      simp at hv; rcases hv with rfl | rfl <;> simp
    rw [natWord_length] at this; omega
  refine Hs.then (scanVars_spec [kN, kKd] (by decide) (by decide) [c.n, kindTag c.kind] rfl a3 c3 _ hin3' L hvb
    (by omega) (by rw [lc3]; omega)) (fun b4 ⟨e4, s4⟩ n4 hn4 => ?_)
  have hin4 := s4.tail hin3'
  refine Hs.then (skipCircuit_spec C L b4 s4.constants c.first _ hin4 (by omega) (by omega)
    (by rw [s4.bytes, lc3]; omega)) (fun b5 s5 n5 hn5 => ?_)
  have hin5 := s5.tail hin4
  refine Hs.then (skipCircuit_spec C L b5 s5.constants c.second _ hin5 (by omega) (by omega)
    (by rw [s5.bytes, s4.bytes, lc3]; omega)) (fun b6 s6 n6 hn6 => ?_)
  have hin6 := s6.tail hin5
  refine Hs.then (skipNatList_spec C L b6 s6.constants c.parity _ hin6 (by omega) (by omega)
    (by rw [s6.bytes, s5.bytes, s4.bytes, lc3]; omega)) (fun b7 s7 n7 hn7 => ?_)
  have hin7 := s7.tail hin6
  refine Hs.last (skipRat_spec C L b7 s7.constants c.radius _ hin7 (by omega) (by omega)
    (by rw [s7.bytes, s6.bytes, s5.bytes, s4.bytes, lc3]; omega)) (fun b8 s8 n8 hn8 => ?_)
  have hin8 := s8.tail hin7
  have sAll := (((s4.then_scanned s5).then_scanned s6).then_scanned s7).then_scanned s8
  have hu := sAll.unchanged
  simp only [Prod.mk.injEq] at hu
  have hT : ∀ y ∈ [kN, kKd] ++ atomScratch ++ gateListScratch ++ gateListScratch ++ scalarListScratch ++ atomScratch,
      y ∈ t0 :: scanCallT := by decide
  have fr3 : Fr a a3 (t0 :: scanCallT) := fr3'.weaken (by decide)
  have v4N : b4.env kN = c.n := e4 (kN, c.n) (by simp)
  have v4K : b4.env kKd = kindTag c.kind := e4 (kKd, kindTag c.kind) (by simp)
  have frl : ∀ y ∈ [kN, kKd], b8.env y = b4.env y := by
    intro y hy
    have := ((s5.then_scanned s6).then_scanned s7).then_scanned s8
    exact this.registers y (by revert hy y; decide)
  refine ⟨⟨by rw [frl kN (by simp), v4N], by rw [frl kKd (by simp), v4K], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fr3.trans (sAll.registers.weaken hT), sAll.constants, hin8⟩, ?_⟩
  · rw [sAll.bytes, lc3]; omega
  · rw [sAll.pos, ip3]; omega
  · rw [hu.1, ha3d]; rfl
  · rw [hu.2.1, ha3d]; rfl
  · rw [hu.2.2.1, ha3d]; rfl
  · rw [hu.2.2.2.1, ha3d]; rfl
  · rw [hu.2.2.2.2.1, ha3d]; rfl
  · rw [hu.2.2.2.2.2, ha3d]; rfl
  · -- the cost
    have p2 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have p1 : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
    have hn5' : n5 ≤ 1000 * (L + 1) ^ 3 := hn5
    have hn6' : n6 ≤ 1000 * (L + 1) ^ 3 := hn6
    have hn7' : n7 ≤ 100 * (L + 1) ^ 2 := hn7
    have hn8' : n8 ≤ 200 * (L + 1) := hn8
    simp only [List.length_cons, List.length_nil] at hn4
    unfold scanCallCost
    nlinarith

end NearQuarticWires.Reconstruct
