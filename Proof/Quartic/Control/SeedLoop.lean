import Proof.Quartic.Control.Budget
import Proof.Quartic.Greedy.Loop
import Proof.Quartic.Program.Output

/-!
# The control of the `S` rounds of Step 3

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, with the cost of `prop:time`
(`2S` child evaluations), and the parameters of `sec:params`.

`seedLoop : Greedy.SeedLoop B1 B2` is the program `Control.seedP` of the child word function, packaged by
`Expand.PolyTab.wordFunction_of_ideal` (imported from `Proof.Gates.Expand.PolyTabPack`):

* on a dispatched call, the word after Step 2 is `true :: callWord c ++ parametersWord p ++ …`
  (`certWord_of_dispatch`); the program reads `S`, runs the `S` rounds on the child objective and writes
  `frame (certWord ++ seedSuffix R)` (`Control.seedP_dispatched`, `Greedy.seedSuffix_of_dispatch`);
* on any other call the word starts with `false` and is copied (`Control.seedP_copy`).

The cost is `K (S + 1)(childBound + |certWord| + S + 1)`. Reading `S` costs `O(|callWord| log(|callWord| + n))`
(`Control.readCost_le`); the logarithm is at most a constant times `S + 1` by the parameter rules
(`natBitLength_le_seedRounds`, `Control.natBitLength_call_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (Call callWord)
open NearQuarticWires.Program NearQuarticWires.Greedy
open NearCubicGates.Close.WordPrograms (WXExec)

/-! ## The parameters -/

theorem mu_pos (n : ℕ) (h : 4 ≤ n) : 1 ≤ NearCubicGates.Target.mu n := by
  unfold NearCubicGates.Target.mu NearCubicGates.Target.lambda
  have h1 : 1 < Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by omega)
  exact Nat.clog_pos (by norm_num) h1

/-- The nineteen parameters before `S` in `Program.parametersWord`. -/
def params19 (p : Cells.Parameters) : List ℕ :=
  [p.lambda, p.mu, p.m, p.r, p.s, p.b, p.k, p.N, p.Jmax, p.T, p.tau, p.U, p.Xmax, p.dstar, p.omega1, p.omega2,
    p.MF, p.Q, p.ellf]

/-- The parameters after `S`. -/
def paramsTail (p : Cells.Parameters) : List Bool :=
  natWord p.NatAtoms ++ natWord p.childCap ++
    natWord p.Uocc ++ natWord p.Dmax ++ natWord p.BN ++ natWord p.P ++ natWord p.e ++ natWord p.hE ++
    natWord p.h ++ natWord p.Lw ++ NearCubicGates.Close.Interfaces.ratWord p.pi0 ++
    NearCubicGates.Close.Interfaces.ratWord p.eta ++ natWord p.Qexp ++
    NearCubicGates.Close.Interfaces.listWord natWord (p.primes.sort (· ≤ ·)) ++ natWord p.Dprime ++ natWord p.L2 ++
    natWord p.M1 ++ natWord p.J ++ natWord p.A ++ natWord p.Lambda ++
    NearCubicGates.Close.Interfaces.ratWord p.ell0 ++ NearCubicGates.Close.Interfaces.listWord natWord p.factors

theorem params19_length (p : Cells.Parameters) : (params19 p).length = 19 := rfl

theorem parametersWord_split (p : Cells.Parameters) :
    parametersWord p = (params19 p).flatMap natWord ++ natWord p.S ++ paramsTail p := by
  simp [parametersWord, params19, paramsTail, List.append_assoc]

variable {B1 B2 : ℕ}

/-- **The word after Step 2 of a dispatched call** begins with the tag, the call word, the nineteen parameters
before `S`, and `S`. -/
theorem certWord_of_dispatch {c : Call} {p : Selected c} (h : dispatch B1 B2 c = some p) (w : List Bool) :
    certWord B1 B2 c w = [true] ++ callWord c ++ (params19 p.1).flatMap natWord ++ natWord p.1.S ++
      (paramsTail p.1 ++ frame (witnessPrefix c p.1 w) ++ frame (certifiedBits (runCall c p w))) := by
  unfold certWord stageWord
  rw [h]
  simp [parametersWord_split, List.append_assoc]

/-- The word after Step 2 of any other call begins with the tag `0`. -/
theorem certWord_of_not_dispatch {c : Call} (h : dispatch B1 B2 c = none) (w : List Bool) :
    certWord B1 B2 c w = false :: NearCubicGates.Close.Interfaces.outputWord (admittedValue B1 B2 Builder.value c w) := by
  unfold certWord stageWord
  rw [h]

/-- **The bit length of `n` is paid by the rounds** on a dispatched call. -/
theorem natBitLength_le_seedRounds {c : Call} {p : Selected c} (h : dispatch B1 B2 c = some p) :
    natBitLength c.n ≤ p.1.S + 1 := by
  have hr := Cells.prepare_spec _ p.1 p.2
  have h4 : 4 ≤ c.n := (dispatch_admitted h).1.1
  exact natBitLength_le_rounds c.n p.1.mu p.1.r p.1.s p.1.k p.1.S p.1.ellf p.1.Qexp
    (by rw [hr.mu_eq]; exact mu_pos _ h4) hr.r_eq hr.r_bound hr.s_eq hr.k_eq hr.ellf_eq
    (by rw [hr.S_eq, hr.m_eq])


/-! ## The program, its cost and its capacity -/

/-- The cost of the program of Step 3 on a call: `seedCost` on a dispatched call, the copy on any other call. -/
noncomputable def seedRun (B1 B2 : ℕ) (childBound : Call → List Bool → ℕ) (c : Call) (w : List Bool) : ℕ :=
  match dispatch B1 B2 c with
  | some p => seedCost (certWord B1 B2 c w).length p.1.S (readCost c (params19 p.1) p.1.S) (childBound c w)
  | none => writeOutCost (certWord B1 B2 c w).length 0 + 6

/-- The register capacity of the program of Step 3 on a call. -/
noncomputable def seedCap (B1 B2 : ℕ) (childBound : Call → List Bool → ℕ) (c : Call) (w : List Bool) : ℕ :=
  2 ^ ((certWord B1 B2 c w).length + 2) +
    10 * ((certWord B1 B2 c w).length + seedRounds B1 B2 c + childBound c w + 10)

/-- The constant of the cost of `seedLoop`. -/
def seedK (B2 : ℕ) : ℕ := 880 * (2 * B2 + 34) + 10000

/-- **The run of the program of Step 3**: on every call, from the start on the word after Step 2, the program of the
child word function writes exactly `frame (certWord ++ seedSuffix R)` on the output stream within `seedRun`. -/
theorem seedP_run (R : ChildRequest B1 B2 → ℤ) (childBudget : ChildRequest B1 B2 → ℕ)
    (childBound : Call → List Bool → ℕ)
    (f : WordFunction (ChildRequest B1 B2) childInput (fun q => NearCubicGates.Close.Interfaces.intWord (R q))
      childBudget)
    (hbound : ∀ q : ChildRequest B1 B2, childBudget q ≤ childBound q.call q.witness) (c : Call) (w : List Bool) :
    ∃ τ, WXExec (seedCap B1 B2 childBound c w) (seedP f.program) (seedStart _ (certWord B1 B2 c w)) τ
        (seedRun B1 B2 childBound c w) ∧
      τ.st (sOUT _) = frame (certWord B1 B2 c w ++ seedSuffix B1 B2 R c w) := by
  cases hd : dispatch B1 B2 c with
  | none =>
    have hw := certWord_of_not_dispatch hd w
    obtain ⟨τ, e, hout⟩ := seedP_copy f.program (seedCap B1 B2 childBound c w) (certWord B1 B2 c w) _ hw
      (by unfold seedCap; have := Nat.lt_two_pow_self (n := (certWord B1 B2 c w).length + 2); omega)
    refine ⟨τ, ?_, ?_⟩
    · unfold seedRun; rw [hd]; exact e
    · rw [hout, seedSuffix_of_not_dispatch _ hd, List.append_nil]
  | some p =>
    have hw := certWord_of_dispatch hd w
    have hS : seedRounds B1 B2 c = p.1.S := by rw [seedRounds_of_dispatch hd w, seedLength_runCall]
    set cw := certWord B1 B2 c w with hcw
    have hlen := congrArg List.length hw
    simp only [List.length_append] at hlen
    have hcwl : cw.length = (certWord B1 B2 c w).length := rfl
    have hpw : 2 ^ (cw.length + 2) = 2 ^ ((certWord B1 B2 c w).length + 2) := rfl
    obtain ⟨τ, e, hout⟩ := seedP_dispatched f (seedCap B1 B2 childBound c w) cw c (params19 p.1) p.1.S _ hw
      (params19_length p.1)
      (readFits_of_le c (params19 p.1) p.1.S _ (by
        unfold seedCap
        have : 2 ^ ((callWord c).length + ((params19 p.1).flatMap natWord).length + (natWord p.1.S).length + 2) ≤
            2 ^ (cw.length + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega))
      (prefixObjective R c w p hd)
      (fun π hπ => (⟨c, w, p, hd, π, by rw [seedLength_runCall]; exact hπ⟩ : ChildRequest B1 B2))
      (fun π hπ => ⟨rfl, by
        unfold prefixObjective
        rw [dif_pos (by rw [seedLength_runCall]; exact hπ)]⟩)
      (childBound c w) (fun π hπ => hbound _)
      (by unfold seedCap; rw [hS]; have := Nat.lt_two_pow_self (n := cw.length + 2); omega)
    refine ⟨τ, ?_, ?_⟩
    · unfold seedRun; rw [hd]; exact e
    · rw [hout, seedSuffix_of_dispatch _ hd, seedLength_runCall]
      simp only [Machine.chosenSeed, List.append_assoc]


/-- The arithmetic of the cost of Step 3. -/
theorem seedCost_arith (B2 W S B r Λ cl xl : ℕ) (hΛ : Λ ≤ (2 * B2 + 32) * (S + 1)) (hcl : cl ≤ W) (hxl : xl ≤ W)
    (hr : r ≤ 440 * (Λ + 2) * (cl + 1) + 21 * xl + (S + 3) * (80 * S + 120) + 20) :
    2 * seedCost W S r B + 2 ≤ seedK B2 * (S + 1) * (B + W + S + 1) := by
  have hY1 : 1 ≤ S + 1 := by omega
  have hP : B + W + S + 1 ≤ (S + 1) * (B + W + S + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h1 : 440 * (Λ + 2) * (cl + 1) ≤ 440 * (2 * B2 + 34) * ((S + 1) * (B + W + S + 1)) := by
    have a1 : Λ + 2 ≤ (2 * B2 + 34) * (S + 1) := by
      have e : (2 * B2 + 34) * (S + 1) = (2 * B2 + 32) * (S + 1) + 2 * (S + 1) := by ring
      omega
    have a2 : cl + 1 ≤ B + W + S + 1 := by omega
    calc 440 * (Λ + 2) * (cl + 1) ≤ 440 * ((2 * B2 + 34) * (S + 1)) * (B + W + S + 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) a2
      _ = 440 * (2 * B2 + 34) * ((S + 1) * (B + W + S + 1)) := by ring
  have h2 : (S + 3) * (80 * S + 120) ≤ 360 * ((S + 1) * (B + W + S + 1)) := by
    calc (S + 3) * (80 * S + 120) ≤ (3 * (S + 1)) * (120 * (B + W + S + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 360 * ((S + 1) * (B + W + S + 1)) := by ring
  have h3 : S * (2000 * (W + S + B + 2) + 4) ≤ 4004 * ((S + 1) * (B + W + S + 1)) := by
    calc S * (2000 * (W + S + B + 2) + 4) ≤ (S + 1) * (4004 * (B + W + S + 1)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 4004 * ((S + 1) * (B + W + S + 1)) := by ring
  have hK : seedK B2 * (S + 1) * (B + W + S + 1) =
      2 * (440 * (2 * B2 + 34) * ((S + 1) * (B + W + S + 1))) + 10000 * ((S + 1) * (B + W + S + 1)) := by
    unfold seedK; ring
  rw [hK]
  unfold seedCost preludeCost roundCost writeOutCost
  linarith

/-- **The cost of Step 3** fits `K (S + 1)(childBound + |certWord| + S + 1)` with `K = seedK B2`. -/
theorem seedRun_le (childBound : Call → List Bool → ℕ) (c : Call) (w : List Bool) :
    2 * seedRun B1 B2 childBound c w + 2 ≤ seedK B2 * (seedRounds B1 B2 c + 1) *
      (childBound c w + (certWord B1 B2 c w).length + seedRounds B1 B2 c + 1) := by
  cases hd : dispatch B1 B2 c with
  | none =>
    have h0 : seedRounds B1 B2 c = 0 := by unfold seedRounds; rw [hd]
    unfold seedRun; rw [hd, h0]
    unfold writeOutCost seedK
    nlinarith
  | some p =>
    have hS : seedRounds B1 B2 c = p.1.S := by rw [seedRounds_of_dispatch hd w, seedLength_runCall]
    unfold seedRun; rw [hd, hS]
    have hw := certWord_of_dispatch hd w
    have hlen := congrArg List.length hw
    simp only [List.length_append] at hlen
    have hcl : (callWord c).length ≤ NearCubicGates.Close.CounterAsm.callBound B2 c.n :=
      callWord_length_le (dispatch_admitted hd).1
    exact seedCost_arith B2 _ p.1.S _ _ _ _ _
      (natBitLength_call_le B2 c.n (callWord c).length p.1.S hcl (natBitLength_le_seedRounds hd))
      (by omega) (by omega) (readCost_le c (params19 p.1) p.1.S)


/-! ## The control -/

/-- **The control of the `S` rounds of Step 3** (`Greedy.SeedLoop`, paper/paper.tex with
`prop:time`): for every integer objective `R` and every word function computing it on the child
evaluations, the program `seedP` of that word function, packaged by `Expand.PolyTab.wordFunction_of_ideal`, maps
the word after Step 2 to `frame (certWord ++ seedSuffix R)` within `seedK B2 · (S + 1)(childBound + |certWord| + S + 1)`
steps. -/
noncomputable def seedLoop (B1 B2 : ℕ) : SeedLoop B1 B2 where
  K := seedK B2
  program := fun R childBudget childBound child hbound =>
    NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (seedP child.program) (sOUT _) (by simp)
      (fun r => seedCap B1 B2 childBound r.1 r.2) (fun _ _ => 0) (fun r => seedRun B1 B2 childBound r.1 r.2)
      (fun r => seedRun_le childBound r.1 r.2)
      (fun r => ⟨rfl, seedP_run R childBudget childBound child hbound r.1 r.2⟩)

end NearQuarticWires.Control
