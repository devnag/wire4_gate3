import Proof.Quartic.Reconstruct.PrintScanCall

/-!
# Reading the parameters, counting

Paper: `sec:params`, paper/paper.tex (the parameters), and Step 3 of `sec:algorithm`.

`scanParamsS` reads the parameter word (`Program.parametersWord`) in its literal order, counting its bits
(`scanParamsS_spec`): it keeps `k`, `ω_1`, `ω_2`, `h_E`, `M_1`, `J`, `A`, `Λ` in variables and the primes `𝒫`
(increasing) and the rate factors in the stores `sPr`, `sF`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord ratWord)
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx}

/-- The parameter `k`. -/
def kK : Fin VV := ⟨89, by decide⟩
/-- The parameter `ω_1`. -/
def kO1 : Fin VV := ⟨90, by decide⟩
/-- The parameter `ω_2`. -/
def kO2 : Fin VV := ⟨91, by decide⟩
/-- The parameter `h_E`. -/
def kE : Fin VV := ⟨92, by decide⟩
/-- The parameter `J`. -/
def kJ1 : Fin VV := ⟨93, by decide⟩
/-- The store of the primes. -/
def sPr : Fin MM := ⟨1, by decide⟩

/-- Read the parameter word, counting. -/
def scanParamsS : St VV MM :=
  .seq (scanSkipS 6) (.seq (scanVars [kK]) (.seq (scanSkipS 7) (.seq (scanVars [kO1, kO2]) (.seq (scanSkipS 11)
  (.seq (scanVars [kE]) (.seq (scanSkipS 2) (.seq skipRat (.seq skipRat (.seq (scanSkipS 1) (.seq (listInto sPr kPc)
  (.seq (scanSkipS 2) (.seq (scanVars [kM, kJ1, kA, kL]) (.seq skipRat (listInto sF kFc))))))))))))))

/-- The variables written by `scanParamsS`. -/
def scanParamsT : List (Fin VV) := [kK, kO1, kO2, kE, kM, kJ1, kA, kL] ++ listIntoT

/-- The parameter word in the pieces read by `scanParamsS`. -/
theorem parametersWord_split (p : Cells.Parameters) :
    Program.parametersWord p =
      (List.ofFn ![p.lambda, p.mu, p.m, p.r, p.s, p.b]).flatMap natWord ++ ([p.k].flatMap natWord ++
      ((List.ofFn ![p.N, p.Jmax, p.T, p.tau, p.U, p.Xmax, p.dstar]).flatMap natWord ++
      ([p.omega1, p.omega2].flatMap natWord ++
      ((List.ofFn ![p.MF, p.Q, p.ellf, p.S, p.NatAtoms, p.childCap, p.Uocc, p.Dmax, p.BN, p.P, p.e]).flatMap natWord ++
      ([p.hE].flatMap natWord ++ ((List.ofFn ![p.h, p.Lw]).flatMap natWord ++ (ratWord p.pi0 ++ (ratWord p.eta ++
      ((List.ofFn ![p.Qexp]).flatMap natWord ++ (listWord natWord (p.primes.sort (· ≤ ·)) ++
      ((List.ofFn ![p.Dprime, p.L2]).flatMap natWord ++ ([p.M1, p.J, p.A, p.Lambda].flatMap natWord ++
      (ratWord p.ell0 ++ listWord natWord p.factors))))))))))))) := by
  simp [Program.parametersWord, List.ofFn_succ, List.append_assoc]

/-! ## Chaining counted reads -/

theorem chain_scan {α : Type} {P : St VV MM} {enc : α → List Bool} {U T : List (Fin VV)} {cost : ℕ → ℕ}
    (hP : ScanSpec P enc U cost) (hU : ∀ y ∈ U, y ∈ T) {a b : DS VV MM} {k : ℕ} {ms : List (Fin MM)}
    (acc : ScannedS a b k T ms) (x : α) (w : List Bool) (hw : enc x = w) (rest : List Bool)
    (hin : C.inp.drop b.ip = w ++ rest) (L : ℕ)
    (hlen : w.length ≤ L) (hW : L + 2 ≤ C.Wd) (hcap : b.env lengthCounter + w.length < 2 ^ C.Wd) :
    Hs C P b (cost L) (fun c => ScannedS a c (k + w.length) T ms ∧ C.inp.drop c.ip = rest ∧
      Fr b c U ∧ c.ram = b.ram ∧ c.rc = b.rc) := by
  subst hw
  refine (hP C L b acc.cst x rest hin hlen hW hcap).mono le_rfl (fun c hc => ?_)
  have hu := hc.unchanged
  simp only [Prod.mk.injEq] at hu
  exact ⟨acc.trans ((ScannedS.of_scanned hc ms).weaken hU (fun _ h => h)), hc.tail hin, hc.registers, hu.2.1,
    hu.2.2.1⟩

theorem chain_vars (xs : List (Fin VV)) (hnd : xs.Nodup) (hx : ∀ x ∈ xs, x ∉ atomScratch ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2)
    {T : List (Fin VV)} (hU : ∀ y ∈ xs ++ atomScratch, y ∈ T) {a b : DS VV MM} {k : ℕ} {ms : List (Fin MM)}
    (acc : ScannedS a b k T ms) (vs : List ℕ) (hl : vs.length = xs.length) (rest : List Bool)
    (hin : C.inp.drop b.ip = vs.flatMap natWord ++ rest) (L : ℕ) (hlen : (vs.flatMap natWord).length ≤ L)
    (hW : L + 2 ≤ C.Wd) (hcap : b.env lengthCounter + (vs.flatMap natWord).length < 2 ^ C.Wd) :
    Hs C (scanVars xs) b (xs.length * (30 * L + 39) + 1) (fun c => (∀ p ∈ xs.zip vs, c.env p.1 = p.2) ∧
      ScannedS a c (k + (vs.flatMap natWord).length) T ms ∧ C.inp.drop c.ip = rest ∧ Fr b c (xs ++ atomScratch) ∧
      c.ram = b.ram ∧ c.rc = b.rc) := by
  have hvb : ∀ v ∈ vs, natBitLength v ≤ L := by
    intro v hv
    have h1 : natBitLength v ≤ (natWord v).length := by rw [natWord_length]; omega
    have h2 : (natWord v).length ≤ (vs.flatMap natWord).length := by
      obtain ⟨l1, l2, hl'⟩ := List.append_of_mem hv
      rw [hl', List.flatMap_append, List.flatMap_cons]; simp only [List.length_append]; omega
    omega
  refine (scanVars_spec xs hnd hx vs hl b acc.cst rest hin L hvb hW hcap).mono le_rfl (fun c ⟨hv, hc⟩ => ?_)
  have hu := hc.unchanged
  simp only [Prod.mk.injEq] at hu
  exact ⟨hv, acc.trans ((ScannedS.of_scanned hc ms).weaken hU (fun _ h => h)), hc.tail hin, hc.registers, hu.2.1,
    hu.2.2.1⟩

theorem chain_list (m : Fin MM) (x : Fin VV) (hx : x ∈ [kPc, kFc]) {T : List (Fin VV)} (hU : ∀ y ∈ listIntoT, y ∈ T) {a b : DS VV MM} {k : ℕ}
    {ms : List (Fin MM)} (hm : m ∈ ms) (acc : ScannedS a b k T ms) (vs : List ℕ) (rest : List Bool)
    (hin : C.inp.drop b.ip = listWord natWord vs ++ rest) (hram : b.ram m = []) (hrc : b.rc m = 0) (L : ℕ)
    (hlen : (listWord natWord vs).length ≤ L) (hW : L + 2 ≤ C.Wd)
    (hcap : b.env lengthCounter + (listWord natWord vs).length < 2 ^ C.Wd) :
    Hs C (listInto m x) b (100 * (L + 1) ^ 2 + 6 * L + vs.length * (30 * L + 36) + 30 * L + 62)
      (fun c => c.env x = vs.length ∧ c.ram m = vs ∧ c.rc m = vs.length ∧
        ScannedS a c (k + (listWord natWord vs).length) T ms ∧
        C.inp.drop c.ip = rest ∧ Fr b c (listIntoTx x) ∧
        (∀ m', m' ≠ m → c.ram m' = b.ram m' ∧ c.rc m' = b.rc m')) := by
  refine (listInto_spec m x hx b acc.cst vs rest hin hram hrc L hlen hW hcap).mono le_rfl
    (fun c ⟨h0, h1, h2, h3, h4⟩ => ⟨h0, h1, h2, acc.trans (h3.weaken (fun y hy => hU y (listIntoTx_sub x hx y hy))
      (by simpa using hm)), h4, h3.fr, fun m' hm' =>
      ⟨h3.ram m' (by simpa using hm'), h3.rc m' (by simpa using hm')⟩⟩)

theorem ScannedS.ofEq {a b : DS VV MM} {k k' : ℕ} {T : List (Fin VV)} {ms : List (Fin MM)} (h : k = k')
    (hs : ScannedS a b k T ms) : ScannedS a b k' T ms := h ▸ hs

theorem length_le_listWord (l : List ℕ) : l.length ≤ (listWord natWord l).length := by
  have := length_le_flatMap_natWord l
  unfold listWord; rw [List.length_append]; omega

end NearQuarticWires.Reconstruct
