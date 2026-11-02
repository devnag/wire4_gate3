import Proof.Quartic.Reconstruct.PrintHead

/-!
# The run of the input reading of the printing stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`printHeadS_spec`: from the start of `gammaWord q` with empty stores and a width covering the call and the
parameters, `printHeadS` reaches a state `HeadDone q` at the end of the input, writing nothing.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (callWord kindTag listWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx} {B1 B2 : ℕ}

theorem J_succ_lt (q : ChildRequest B1 B2) (W : ℕ) (hW : (parametersWord q.selected.1).length + 1 ≤ W) :
    q.selected.1.J + 1 < 2 ^ W := by
  have hs := parametersWord_split q.selected.1
  have hl := congrArg List.length hs
  simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hl
  have h1 := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl q.selected.1.J
  have h2 := natWord_length q.selected.1.J
  have h3 : 2 ^ natBitLength q.selected.1.J < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- **Reading the input of the printing stage.** -/
theorem printHeadS_spec (q : ChildRequest B1 B2) (a : DS VV MM) (hc : Cst a) (hinp : C.inp = gammaWord q)
    (hip : a.ip = 0) (hram : ∀ m, a.ram m = [] ∧ a.rc m = 0)
    (hW : (callWord q.call).length + (parametersWord q.selected.1).length + 6 ≤ C.Wd)
    (hγ : (prepWord B1 B2 q.call q.witness).length < 2 ^ C.Wd) :
    Hs C printHeadS a (printHeadCost q) (fun b => HeadDone q b ∧ b.out = a.out) := by
  have hsplit := gammaWord_split q
  have hpre := prepWord_split q
  have hwp := witnessPrefix_length q
  have hom := omega_half q
  have hγl := congrArg List.length hsplit
  simp only [List.length_cons, List.length_append, RepairOrdinary.frame_length] at hγl
  have hpl := congrArg List.length hpre
  simp only [List.length_cons, List.length_append, RepairOrdinary.frame_length] at hpl
  have hW2 : 2 < 2 ^ C.Wd := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ C.Wd by omega))
  have ho0 := omega_eq q 0
  have ho1 := omega_eq q 1
  simp only [Fin.isValue, if_true, one_ne_zero, if_false] at ho0 ho1
  -- the call
  have hin0 : C.inp.drop a.ip = true :: (callWord q.call ++ (parametersWord q.selected.1 ++ (frame (wpOf q) ++
      (frame (certifiedBits q.cellCall) ++ (frame q.seedPrefix ++ gammaTableWord q))))) := by
    rw [hip, hinp, hsplit, List.drop_zero]
  refine Hx.hs (Hs.then (scanCallS_spec a hc q.call _ hin0 (by omega))
    (fun b1 ⟨n1v, k1v, lc1, ip1, out1, ram1, rc1, kin1, kout1, kc1, fr1, c1, hin1⟩ t1 ht1 => ?_))
  -- the parameters
  refine Hs.then (scanParamsS_spec b1 c1 q.selected.1 _ hin1 (by rw [ram1, rc1]; exact hram sF)
    (by rw [ram1, rc1]; exact hram sPr) (by rw [lc1]; omega))
    (fun b2 ⟨vK, vO1, vO2, vE, vM, vJ, vA, vL, prR, prC, fR, fC, vPc, sc2, hin2⟩ t2 ht2 => ?_)
  have lc2 : b2.env lengthCounter = 1 + (callWord q.call).length + (parametersWord q.selected.1).length := by
    rw [sc2.bytes, lc1]
  -- the length of `prepWord`
  refine Hs.then (wpLenS_spec b2 sc2.cst _ _ _ _ _ vO1 vO2 vJ vK lc2 (by omega) (by omega)
    (J_succ_lt q C.Wd (by omega)) (by rw [← hwp]; omega))
    (fun b3 ⟨vB0, vB1, vPL, vR, sm3, fr3, c3⟩ t3 ht3 => ?_)
  have ip3 : b3.ip = 1 + (callWord q.call).length + (parametersWord q.selected.1).length := by
    rw [sm3.ip, sc2.pos, ip1, hip]; omega
  -- back to the start
  refine Hs.then (rewindS_spec kR (by decide) b3 c3 _ vR (by omega))
    (fun b4r ⟨ip4r, _, out4r, ram4r, rc4r, _, _, _, fr4r, c4r⟩ t4r ht4r => ?_)
  refine Hs.then (hs_copy C kR kPL b4r (by decide)) (fun b4 hb4 t4 ht4 => ?_)
  have ip4 := ip4r
  rw [show b4r.ip = b4.ip by rw [hb4]; rfl] at ip4
  have out4 : b4.out = b3.out := by rw [hb4]; exact out4r
  have ram4 : b4.ram = b3.ram := by rw [hb4]; exact ram4r
  have rc4 : b4.rc = b3.rc := by rw [hb4]; exact rc4r
  have k4 : ∀ y, y ≠ kR → b4.env y = b3.env y := fun y hy => by
    rw [hb4, DS.set_env_ne _ _ hy]; exact fr4r y (by simpa using hy)
  have vR4 : b4.env kR = b3.env kPL := by
    rw [hb4, DS.set_env_self]; exact fr4r kPL (by decide)
  have c4 : Cst b4 := by
    rw [hb4]; exact ⟨by vsimp [c4r.z], by vsimp [c4r.one], by vsimp [c4r.two]⟩
  have st4 : ∀ m, m ∉ [sPr, sF] → b4.ram m = [] ∧ b4.rc m = 0 := fun m hm => by
    rw [ram4, rc4, sm3.ram, sm3.rc, sc2.ram m hm, sc2.rc m hm, ram1, rc1]; exact hram m
  -- copy `prepWord`
  have hin4 : C.inp.drop b4.ip = prepWord B1 B2 q.call q.witness ++ (frame (certifiedBits q.cellCall) ++
      (frame q.seedPrefix ++ gammaTableWord q)) := by
    rw [ip4, ip3, Nat.sub_self, hinp, hsplit, hpre]; simp
  refine Hs.then (rawCopyS_spec sP kR (by decide) b4 c4 _ _ (by rw [vR4, vPL, hpl, hwp]; omega) hin4
    (by rw [(st4 sP (by decide)).1, (st4 sP (by decide)).2]; rfl))
    (fun b5 ⟨im5, hin5, _, c5⟩ t5 ht5 => ?_)
  -- the frames
  refine Hs.then (rawFrameS_spec sZ b5 c5 _ _ hin5 (by
    rw [im5.rco sZ (by decide), im5.ramo sZ (by decide), (st4 sZ (by decide)).1, (st4 sZ (by decide)).2]; rfl) hW2)
    (fun b6 ⟨im6, hin6, c6⟩ t6 ht6 => ?_)
  refine Hs.then (rawFrameS_spec sX b6 c6 _ _ hin6 (by
    rw [im6.rco sX (by decide), im6.ramo sX (by decide), im5.rco sX (by decide), im5.ramo sX (by decide),
      (st4 sX (by decide)).1, (st4 sX (by decide)).2]; rfl) hW2)
    (fun b7 ⟨im7, hin7, c7⟩ t7 ht7 => ?_)
  have hin7' : C.inp.drop b7.ip = frame (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)) ++ [] := by
    rw [hin7, List.append_nil]; rfl
  refine Hs.last (rawFrameS_spec sG b7 c7 _ _ hin7' (by
    rw [im7.rco sG (by decide), im7.ramo sG (by decide), im6.rco sG (by decide), im6.ramo sG (by decide),
      im5.rco sG (by decide), im5.ramo sG (by decide), (st4 sG (by decide)).1, (st4 sG (by decide)).2]; rfl) hW2)
    (fun b8 ⟨im8, hin8, c8⟩ t8 ht8 => ⟨⟨?_, ?_⟩, ?_⟩)
  · -- the values
    have keep : ∀ y, y ∉ [kR, fB, kPL, fE, fM] → b8.env y = b3.env y := by
      intro y hy
      rw [im8.fr y (fun h => hy (by revert h; revert y; decide)), im7.fr y (fun h => hy (by revert h; revert y; decide)),
        im6.fr y (fun h => hy (by revert h; revert y; decide)), im5.fr y (fun h => hy (by revert h; revert y; decide)),
        k4 y (fun h => hy (by rw [h]; decide))]
    have keep2 : ∀ y, y ∉ [kR, fB, kPL, fE, fM, kB0, kB1, kT1] → b8.env y = b2.env y := by
      intro y hy
      rw [keep y (fun h => hy (by revert h; revert y; decide)), fr3 y (fun h => hy (by revert h; revert y; decide))]
    have keep1 : ∀ y ∈ [kN, kKd], b8.env y = b1.env y := by
      intro y hy
      rw [keep2 y (by revert hy y; decide), sc2.fr y (by revert hy y; decide)]
    have r8 : ∀ m, m ≠ sZ → m ≠ sX → m ≠ sG → m ≠ sP → b8.ram m = b4.ram m ∧ b8.rc m = b4.rc m := by
      intro m h1 h2 h3 h4
      exact ⟨by rw [im8.ramo m h3, im7.ramo m h2, im6.ramo m h1, im5.ramo m h4],
        by rw [im8.rco m h3, im7.rco m h2, im6.rco m h1, im5.rco m h4]⟩
    have prr : b8.ram sPr = q.selected.1.primes.sort (· ≤ ·) := by
      rw [(r8 sPr (by decide) (by decide) (by decide) (by decide)).1, ram4, sm3.ram, prR]
    have ffr : b8.ram sF = q.selected.1.factors := by
      rw [(r8 sF (by decide) (by decide) (by decide) (by decide)).1, ram4, sm3.ram, fR]
    refine ⟨by rw [keep1 kN (by simp), n1v], by rw [keep1 kKd (by simp), k1v], by rw [keep2 kK (by decide), vK],
      by rw [keep2 kE (by decide), vE], by rw [keep2 kM (by decide), vM], by rw [keep2 kJ1 (by decide), vJ],
      by rw [keep2 kA (by decide), vA], by rw [keep2 kL (by decide), vL], by rw [keep kB0 (by decide), vB0, hom.1],
      by rw [keep kB1 (by decide), vB1, hom.2], prr, by rw [keep2 kPc (by decide), vPc], ffr, ?_, ?_, ?_, ?_, ?_, ?_,
      c8, ?_⟩
    · rw [im8.ramo sP (by decide), im7.ramo sP (by decide), im6.ramo sP (by decide), im5.ram,
        (st4 sP (by decide)).1, List.nil_append]
    · rw [im8.ramo sZ (by decide), im7.ramo sZ (by decide), im6.ram, im5.ramo sZ (by decide),
        (st4 sZ (by decide)).1, List.nil_append]
    · rw [im8.ram, im7.ramo sG (by decide), im6.ramo sG (by decide), im5.ramo sG (by decide),
        (st4 sG (by decide)).1, List.nil_append]; rfl
    · intro m hm
      simp only [headStores, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [(r8 sPr (by decide) (by decide) (by decide) (by decide)).2, rc4, sm3.rc, prr, prC]
      · rw [(r8 sF (by decide) (by decide) (by decide) (by decide)).2, rc4, sm3.rc, ffr, fC]
      · have e5 := im5.endc (by rw [(st4 sP (by decide)).1, (st4 sP (by decide)).2]; rfl)
        rw [im8.rco sP (by decide), im7.rco sP (by decide), im6.rco sP (by decide), im8.ramo sP (by decide),
          im7.ramo sP (by decide), im6.ramo sP (by decide)]
        exact e5
      · have e5 : b5.rc sZ = (b5.ram sZ).length := by
          rw [im5.rco sZ (by decide), im5.ramo sZ (by decide), (st4 sZ (by decide)).1, (st4 sZ (by decide)).2]; rfl
        rw [im8.rco sZ (by decide), im7.rco sZ (by decide), im8.ramo sZ (by decide), im7.ramo sZ (by decide)]
        exact im6.endc e5
      · have e6 : b6.rc sX = (b6.ram sX).length := by
          rw [im6.rco sX (by decide), im6.ramo sX (by decide), im5.rco sX (by decide), im5.ramo sX (by decide),
            (st4 sX (by decide)).1, (st4 sX (by decide)).2]; rfl
        rw [im8.rco sX (by decide), im8.ramo sX (by decide)]
        exact im7.endc e6
      · have e7 : b7.rc sG = (b7.ram sG).length := by
          rw [im7.rco sG (by decide), im7.ramo sG (by decide), im6.rco sG (by decide), im6.ramo sG (by decide),
            im5.rco sG (by decide), im5.ramo sG (by decide), (st4 sG (by decide)).1, (st4 sG (by decide)).2]; rfl
        exact im8.endc e7
    · intro m hm
      have hm' : m ∉ [sPr, sF] := fun h => hm (by simp only [headStores, List.mem_cons] at h ⊢; tauto)
      have h1 : m ≠ sZ := fun h => hm (by rw [h]; decide)
      have h2 : m ≠ sX := fun h => hm (by rw [h]; decide)
      have h3 : m ≠ sG := fun h => hm (by rw [h]; decide)
      have h4 : m ≠ sP := fun h => hm (by rw [h]; decide)
      rw [(r8 m h1 h2 h3 h4).1, (r8 m h1 h2 h3 h4).2]
      exact st4 m hm'
    · rw [im8.ip, im7.ip, im6.ip, im5.ip, ip4, ip3, Nat.sub_self, hγl, hpl]
      simp only [listWord, List.length_append, RepairOrdinary.frame_length]
      unfold gammaTableWord
      simp only [RepairOrdinary.frame_length, listWord, List.length_append]
      omega
    · rw [im8.fr kPL (by decide), im7.fr kPL (by decide), im6.fr kPL (by decide), im5.fr kPL (by decide),
        k4 kPL (by decide), vPL, hpl, hwp]
      omega
  · rw [im8.out, im7.out, im6.out, im5.out, out4, sm3.out, sc2.out, out1]
  · -- the cost
    have hgt : (gammaTableWord q).length =
        2 * (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length + 1 := by
      unfold gammaTableWord; rw [RepairOrdinary.frame_length]
    unfold printHeadCost
    omega

end NearQuarticWires.Reconstruct
