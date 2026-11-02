import Proof.Quartic.Reconstruct.PrintScanParams

/-!
# The run of the parameter scan

Paper: `sec:params`, paper/paper.tex, and Step 3 of `sec:algorithm`.

`scanParamsS_spec`: from the parameter word, `scanParamsS` keeps `k, ω_1, ω_2, h_E, M_1, J, A, Λ` in variables and the
primes and the rate factors in stores, and counts the bits of the word.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord ratWord)
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx}

/-- The cost of `scanParamsS` for a parameter word of `L` bits. -/
def scanParamsCost (L : ℕ) : ℕ := 4000 * (L + 1) ^ 2

theorem scanParams_cost_arith (L n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 l11 l15 : ℕ)
    (h1 : n1 ≤ 6 * (66 * (L + 1) + 1) + 1) (h2 : n2 ≤ 1 * (30 * L + 39) + 1) (h3 : n3 ≤ 7 * (66 * (L + 1) + 1) + 1)
    (h4 : n4 ≤ 2 * (30 * L + 39) + 1) (h5 : n5 ≤ 11 * (66 * (L + 1) + 1) + 1) (h6 : n6 ≤ 1 * (30 * L + 39) + 1)
    (h7 : n7 ≤ 2 * (66 * (L + 1) + 1) + 1) (h8 : n8 ≤ 200 * (L + 1)) (h9 : n9 ≤ 200 * (L + 1))
    (h10 : n10 ≤ 1 * (66 * (L + 1) + 1) + 1)
    (h11 : n11 ≤ 100 * (L + 1) ^ 2 + 6 * L + l11 * (30 * L + 36) + 30 * L + 62)
    (h12 : n12 ≤ 2 * (66 * (L + 1) + 1) + 1) (h13 : n13 ≤ 4 * (30 * L + 39) + 1) (h14 : n14 ≤ 200 * (L + 1))
    (h15 : n15 ≤ 100 * (L + 1) ^ 2 + 6 * L + l15 * (30 * L + 36) + 30 * L + 62) (hl11 : l11 ≤ L) (hl15 : l15 ≤ L) :
    n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 + n10 + n11 + n12 + n13 + n14 + n15 + 14 ≤ 4000 * (L + 1) ^ 2 := by
  have m11 : l11 * (30 * L + 36) ≤ 36 * (L + 1) ^ 2 := by nlinarith
  have m15 : l15 * (30 * L + 36) ≤ 36 * (L + 1) ^ 2 := by nlinarith
  have p1 : L + 1 ≤ (L + 1) ^ 2 := by nlinarith
  omega

/-- **Reading the parameters.** -/
theorem scanParamsS_spec (a : DS VV MM) (hc : Cst a) (p : Cells.Parameters) (rest : List Bool)
    (hin : C.inp.drop a.ip = Program.parametersWord p ++ rest) (hF : a.ram sF = [] ∧ a.rc sF = 0)
    (hP : a.ram sPr = [] ∧ a.rc sPr = 0)
    (hW : a.env lengthCounter + (Program.parametersWord p).length + 4 ≤ C.Wd) :
    Hs C scanParamsS a (scanParamsCost (Program.parametersWord p).length)
      (fun b => b.env kK = p.k ∧ b.env kO1 = p.omega1 ∧ b.env kO2 = p.omega2 ∧ b.env kE = p.hE ∧ b.env kM = p.M1 ∧
        b.env kJ1 = p.J ∧ b.env kA = p.A ∧ b.env kL = p.Lambda ∧ b.ram sPr = p.primes.sort (· ≤ ·) ∧
        b.rc sPr = (p.primes.sort (· ≤ ·)).length ∧ b.ram sF = p.factors ∧ b.rc sF = p.factors.length ∧
        b.env kPc = (p.primes.sort (· ≤ ·)).length ∧
        ScannedS a b (Program.parametersWord p).length scanParamsT [sPr, sF] ∧ C.inp.drop b.ip = rest) := by
  have hsplit := parametersWord_split p
  have hlen := congrArg List.length hsplit
  simp only [List.length_append] at hlen
  set L := (Program.parametersWord p).length with hLd
  have hWW : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  rw [hsplit] at hin
  simp only [List.append_assoc] at hin
  have acc0 : ScannedS a a 0 scanParamsT [sPr, sF] :=
    ⟨by simp, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, hc, Fr.refl _ _, by simp⟩
  refine Hx.hs (Hs.then (chain_scan (scanSkipS_spec 6) (by decide) acc0 ![p.lambda, p.mu, p.m, p.r, p.s, p.b] ((List.ofFn ![p.lambda, p.mu, p.m, p.r, p.s, p.b]).flatMap natWord) rfl _ hin L (by omega) (by omega) (by rw [acc0.bytes]; omega))
    (fun b1 ⟨acc1, hin1, fr1, ram1, rc1⟩ n1 hn1 => ?_))
  refine Hs.then (chain_vars [kK] (by decide) (by decide) (by decide) acc1 [p.k] rfl _ hin1 L (by omega) (by omega) (by rw [acc1.bytes]; omega))
    (fun b2 ⟨v2, acc2, hin2, fr2, ram2, rc2⟩ n2 hn2 => ?_)
  refine Hs.then (chain_scan (scanSkipS_spec 7) (by decide) acc2 ![p.N, p.Jmax, p.T, p.tau, p.U, p.Xmax, p.dstar] ((List.ofFn ![p.N, p.Jmax, p.T, p.tau, p.U, p.Xmax, p.dstar]).flatMap natWord) rfl _ hin2 L (by omega) (by omega) (by rw [acc2.bytes]; omega))
    (fun b3 ⟨acc3, hin3, fr3, ram3, rc3⟩ n3 hn3 => ?_)
  refine Hs.then (chain_vars [kO1, kO2] (by decide) (by decide) (by decide) acc3 [p.omega1, p.omega2] rfl _ hin3 L (by omega) (by omega) (by rw [acc3.bytes]; omega))
    (fun b4 ⟨v4, acc4, hin4, fr4, ram4, rc4⟩ n4 hn4 => ?_)
  refine Hs.then (chain_scan (scanSkipS_spec 11) (by decide) acc4 ![p.MF, p.Q, p.ellf, p.S, p.NatAtoms, p.childCap, p.Uocc, p.Dmax, p.BN, p.P, p.e] ((List.ofFn ![p.MF, p.Q, p.ellf, p.S, p.NatAtoms, p.childCap, p.Uocc, p.Dmax, p.BN, p.P, p.e]).flatMap natWord) rfl _ hin4 L (by omega) (by omega) (by rw [acc4.bytes]; omega))
    (fun b5 ⟨acc5, hin5, fr5, ram5, rc5⟩ n5 hn5 => ?_)
  refine Hs.then (chain_vars [kE] (by decide) (by decide) (by decide) acc5 [p.hE] rfl _ hin5 L (by omega) (by omega) (by rw [acc5.bytes]; omega))
    (fun b6 ⟨v6, acc6, hin6, fr6, ram6, rc6⟩ n6 hn6 => ?_)
  refine Hs.then (chain_scan (scanSkipS_spec 2) (by decide) acc6 ![p.h, p.Lw] ((List.ofFn ![p.h, p.Lw]).flatMap natWord) rfl _ hin6 L (by omega) (by omega) (by rw [acc6.bytes]; omega))
    (fun b7 ⟨acc7, hin7, fr7, ram7, rc7⟩ n7 hn7 => ?_)
  refine Hs.then (chain_scan skipRat_spec (by decide) acc7 p.pi0 (ratWord p.pi0) rfl _ hin7 L (by omega) (by omega) (by rw [acc7.bytes]; omega))
    (fun b8 ⟨acc8, hin8, fr8, ram8, rc8⟩ n8 hn8 => ?_)
  refine Hs.then (chain_scan skipRat_spec (by decide) acc8 p.eta (ratWord p.eta) rfl _ hin8 L (by omega) (by omega) (by rw [acc8.bytes]; omega))
    (fun b9 ⟨acc9, hin9, fr9, ram9, rc9⟩ n9 hn9 => ?_)
  refine Hs.then (chain_scan (scanSkipS_spec 1) (by decide) acc9 ![p.Qexp] ((List.ofFn ![p.Qexp]).flatMap natWord) rfl _ hin9 L (by omega) (by omega) (by rw [acc9.bytes]; omega))
    (fun b10 ⟨acc10, hin10, fr10, ram10, rc10⟩ n10 hn10 => ?_)
  have st11 : b10.ram sPr = [] ∧ b10.rc sPr = 0 := by
    constructor
    · rw [ram10, ram9, ram8, ram7, ram6, ram5, ram4, ram3, ram2, ram1]; exact hP.1
    · rw [rc10, rc9, rc8, rc7, rc6, rc5, rc4, rc3, rc2, rc1]; exact hP.2
  refine Hs.then (chain_list sPr kPc (by decide) (by decide) (by decide) acc10 (p.primes.sort (· ≤ ·)) _ hin10 st11.1 st11.2 L (by omega) (by omega) (by rw [acc10.bytes]; omega))
    (fun b11 ⟨x11, l11, lr11, acc11, hin11, fr11, o11⟩ n11 hn11 => ?_)
  refine Hs.then (chain_scan (scanSkipS_spec 2) (by decide) acc11 ![p.Dprime, p.L2] ((List.ofFn ![p.Dprime, p.L2]).flatMap natWord) rfl _ hin11 L (by omega) (by omega) (by rw [acc11.bytes]; omega))
    (fun b12 ⟨acc12, hin12, fr12, ram12, rc12⟩ n12 hn12 => ?_)
  refine Hs.then (chain_vars [kM, kJ1, kA, kL] (by decide) (by decide) (by decide) acc12 [p.M1, p.J, p.A, p.Lambda] rfl _ hin12 L (by omega) (by omega) (by rw [acc12.bytes]; omega))
    (fun b13 ⟨v13, acc13, hin13, fr13, ram13, rc13⟩ n13 hn13 => ?_)
  refine Hs.then (chain_scan skipRat_spec (by decide) acc13 p.ell0 (ratWord p.ell0) rfl _ hin13 L (by omega) (by omega) (by rw [acc13.bytes]; omega))
    (fun b14 ⟨acc14, hin14, fr14, ram14, rc14⟩ n14 hn14 => ?_)
  have st15 : b14.ram sF = [] ∧ b14.rc sF = 0 := by
    constructor
    · rw [ram14, ram13, ram12, (o11 sF (by decide)).1, ram10, ram9, ram8, ram7, ram6, ram5, ram4, ram3, ram2, ram1]; exact hF.1
    · rw [rc14, rc13, rc12, (o11 sF (by decide)).2, rc10, rc9, rc8, rc7, rc6, rc5, rc4, rc3, rc2, rc1]; exact hF.2
  refine Hs.last (chain_list sF kFc (by decide) (by decide) (by decide) acc14 p.factors _ hin14 st15.1 st15.2 L (by omega) (by omega) (by rw [acc14.bytes]; omega))
    (fun b15 ⟨x15, l15, lr15, acc15, hin15, fr15, o15⟩ n15 hn15 => ?_)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, l15, lr15, ?_, ScannedS.ofEq (by omega) acc15, hin15⟩, ?_⟩
  · rw [fr15 kK (by decide), fr14 kK (by decide), fr13 kK (by decide), fr12 kK (by decide), fr11 kK (by decide), fr10 kK (by decide), fr9 kK (by decide), fr8 kK (by decide), fr7 kK (by decide), fr6 kK (by decide), fr5 kK (by decide), fr4 kK (by decide), fr3 kK (by decide)]; exact v2 (kK, p.k) (by simp)
  · rw [fr15 kO1 (by decide), fr14 kO1 (by decide), fr13 kO1 (by decide), fr12 kO1 (by decide), fr11 kO1 (by decide), fr10 kO1 (by decide), fr9 kO1 (by decide), fr8 kO1 (by decide), fr7 kO1 (by decide), fr6 kO1 (by decide), fr5 kO1 (by decide)]; exact v4 (kO1, p.omega1) (by simp)
  · rw [fr15 kO2 (by decide), fr14 kO2 (by decide), fr13 kO2 (by decide), fr12 kO2 (by decide), fr11 kO2 (by decide), fr10 kO2 (by decide), fr9 kO2 (by decide), fr8 kO2 (by decide), fr7 kO2 (by decide), fr6 kO2 (by decide), fr5 kO2 (by decide)]; exact v4 (kO2, p.omega2) (by simp)
  · rw [fr15 kE (by decide), fr14 kE (by decide), fr13 kE (by decide), fr12 kE (by decide), fr11 kE (by decide), fr10 kE (by decide), fr9 kE (by decide), fr8 kE (by decide), fr7 kE (by decide)]; exact v6 (kE, p.hE) (by simp)
  · rw [fr15 kM (by decide), fr14 kM (by decide)]; exact v13 (kM, p.M1) (by simp)
  · rw [fr15 kJ1 (by decide), fr14 kJ1 (by decide)]; exact v13 (kJ1, p.J) (by simp)
  · rw [fr15 kA (by decide), fr14 kA (by decide)]; exact v13 (kA, p.A) (by simp)
  · rw [fr15 kL (by decide), fr14 kL (by decide)]; exact v13 (kL, p.Lambda) (by simp)
  · rw [(o15 sPr (by decide)).1, ram14, ram13, ram12]; exact l11
  · rw [(o15 sPr (by decide)).2, rc14, rc13, rc12]; exact lr11
  · rw [fr15 kPc (by decide), fr14 kPc (by decide), fr13 kPc (by decide), fr12 kPc (by decide)]; exact x11
  · -- the cost
    have hl11 := length_le_listWord (p.primes.sort (· ≤ ·))
    have hl15 := length_le_listWord p.factors
    have := scanParams_cost_arith L n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 (p.primes.sort (· ≤ ·)).length
      p.factors.length hn1 (by simpa using hn2) hn3 (by simpa using hn4) hn5 (by simpa using hn6) hn7 hn8 hn9 hn10 hn11
      hn12 (by simpa using hn13) hn14 hn15 (by omega) (by omega)
    unfold scanParamsCost
    omega

end NearQuarticWires.Reconstruct
