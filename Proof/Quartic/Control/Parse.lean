import Proof.Quartic.Control.Output
import Proof.Gates.Codec.Circuit

/-!
# Reading the number of rounds

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `sec:params`: the number of
rounds is the parameter `S = 2mℓ_f`. On a dispatched call the word after Step 2 is
`true :: callWord c ++ parametersWord p ++ …` (`Program.certWord`), and `S` is the twentieth number of
`parametersWord p`.

* `skipNats`, `skipNats_exec`: move past a list of numbers `natWord x₁ ++ … ++ natWord x_m` on a framed stream;
* `ReadFits`: the register capacity holds every number read;
* `readS`, `readS_exec`: from the framed word, move past the tag, the call word (`Codec.skipNat`, `skipCircuit`,
  `skipList`, `skipInt`, imported from `Proof.Gates.Codec`) and the first nineteen parameters, then read `S` into a
  register (`ParseNat.readNatM`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp readNatM readNatM_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ}

theorem enc_true (w : List Bool) : enc true w = marks w := rfl

/-- Move past `m` numbers on the framed stream `i`. -/
def skipNats (i : Fin (ns + 1)) (f c : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | m + 1 => .seq (NearCubicGates.Close.Codec.skipNat true i f c) (skipNats i f c m)

/-- The cost of moving past the numbers `xs`. -/
def natsCost (xs : List ℕ) : ℕ := (xs.map fun x => 20 * natBitLength x + 21).sum

theorem skipNats_exec (cap : ℕ) (i : Fin (ns + 1)) (f c : Fin nr) (hfc : f ≠ c) :
    ∀ (xs : List ℕ) (pre rest : List Bool) (σ : WState ns nr), σ.st i = pre ++ marks (xs.flatMap natWord) ++ rest →
      σ.sh i = pre.length → σ.val f = 0 → σ.val c = 0 → (∀ x ∈ xs, natBitLength x + 1 ≤ cap) →
      WExec cap (skipNats i f c xs.length) σ (σ.seth i (pre.length + 2 * (xs.flatMap natWord).length))
        (natsCost xs)
  | [], pre, rest, σ, _, hsh, _, _, _ => by
    simp only [List.length_nil, skipNats, List.flatMap_nil, Nat.mul_zero, Nat.add_zero, natsCost, List.map_nil,
      List.sum_nil]
    rw [← hsh]
    refine WExec.cast cap (WExec.skip σ) ?_ le_rfl
    refine WState.eq ?_ rfl rfl rfl
    funext q; by_cases hq : q = i
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  | x :: xs, pre, rest, σ, hst, hsh, hf, hc, hcap => by
    have e1 := NearCubicGates.Close.Codec.skipNat_spec cap true i f c hfc x pre (marks (xs.flatMap natWord) ++ rest) σ
      (by rw [hst, enc_true]; simp [marks_append, List.append_assoc]) hsh hf hc (hcap x (by simp))
    have e2 := skipNats_exec cap i f c hfc xs (pre ++ marks (natWord x)) rest
      (σ.seth i (pre.length + stp true * (natWord x).length))
      (by simp only [WState.seth_st]; rw [hst]; simp [marks_append, List.append_assoc])
      (by simp [stp, marks_length]) hf hc (fun y hy => hcap y (by simp [hy]))
    refine WExec.cast cap (WExec.seq e1 e2) ?_ ?_
    · refine WState.eq ?_ rfl rfl rfl
      funext q; by_cases hq : q = i
      · subst hq; simp [marks_length]; ring
      · simp [Function.update_of_ne hq]
    · simp [natsCost]


/-! ## The number of rounds -/

/-- The register capacity holds every number read on the way to `S`: the numbers of the call, the nineteen
parameters `xs` before `S`, and `S`. -/
structure ReadFits (cap : ℕ) (c : Call) (xs : List ℕ) (S : ℕ) : Prop where
  n : natBitLength c.n + 1 ≤ cap
  kind : natBitLength (kindTag c.kind) + 1 ≤ cap
  first : NearCubicGates.Close.Codec.CircuitFits cap c.first
  second : NearCubicGates.Close.Codec.CircuitFits cap c.second
  parLen : 2 ^ (natBitLength c.parity.length + 1) ≤ cap
  parLen' : c.parity.length ≤ cap
  par : ∀ x ∈ c.parity, natBitLength x + 1 ≤ cap
  num : natBitLength c.radius.num.natAbs + 2 ≤ cap
  den : natBitLength c.radius.den + 1 ≤ cap
  params : ∀ x ∈ xs, natBitLength x + 1 ≤ cap
  rounds : 2 ^ (natBitLength S + 1) ≤ cap

/-- **Reading `S`**: past the tag, the call word and nineteen parameters, then `S` into register `G 6`. With `m`
in place of nineteen, the `m+1`-th parameter is read. -/
def readS (IN : Fin (ns + 1)) (G : Fin 7 ↪ Fin nr) (m : ℕ := 19) : WM ns nr :=
  .seq (.fwd IN) (.seq (.fwd IN)
  (.seq (NearCubicGates.Close.Codec.skipNat true IN (G 0) (G 1))
  (.seq (NearCubicGates.Close.Codec.skipNat true IN (G 0) (G 1))
  (.seq (NearCubicGates.Close.Codec.skipCircuit true IN (G 0) (G 1) (G 2) (G 3) (G 4) (G 5))
  (.seq (NearCubicGates.Close.Codec.skipCircuit true IN (G 0) (G 1) (G 2) (G 3) (G 4) (G 5))
  (.seq (NearCubicGates.Close.Codec.skipList true IN (G 0) (G 1) (G 2) (G 4) (G 5)
      (NearCubicGates.Close.Codec.skipNat true IN (G 0) (G 1)))
  (.seq (NearCubicGates.Close.Codec.skipInt true IN (G 0) (G 1))
  (.seq (NearCubicGates.Close.Codec.skipNat true IN (G 0) (G 1))
  (.seq (skipNats IN (G 0) (G 1) m)
  (readNatM true IN (G 0) (G 1) (G 6) (G 4) (G 5)))))))))))

/-- The cost of `readS`. -/
def readCost (c : Call) (xs : List ℕ) (S : ℕ) : ℕ :=
  1 + 1 + (1 + 1 + ((20 * natBitLength c.n + 20) + 1 + ((20 * natBitLength (kindTag c.kind) + 20) + 1 +
    (NearCubicGates.Close.Codec.circuitCost c.first + 1 + (NearCubicGates.Close.Codec.circuitCost c.second + 1 +
    (NearCubicGates.Close.Codec.skipListCost c.parity.length (c.parity.map fun x => 20 * natBitLength x + 20) + 1 +
    (NearCubicGates.Close.Codec.skipIntCost c.radius.num + 1 + ((20 * natBitLength c.radius.den + 20) + 1 +
    (natsCost xs + 1 + (natBitLength S + 2) * (40 * 2 ^ natBitLength S + 40))))))))))

theorem callWord_split (c : Call) :
    NearCubicGates.Close.Interfaces.callWord c = natWord c.n ++ natWord (kindTag c.kind) ++ circuitWord c.first ++
      circuitWord c.second ++ listWord natWord c.parity ++ NearCubicGates.Close.Interfaces.intWord c.radius.num ++
      natWord c.radius.den := by
  simp [NearCubicGates.Close.Interfaces.callWord, ratWord, List.append_assoc]

theorem seth_seth (σ : WState ns nr) (i : Fin (ns + 1)) (a b : ℕ) : (σ.seth i a).seth i b = σ.seth i b := by
  refine WState.eq ?_ rfl rfl rfl
  funext q; by_cases hq : q = i
  · subst hq; simp
  · simp [Function.update_of_ne hq]

section ReadS

variable (cap : ℕ) (σ : WState ns nr) (IN : Fin (ns + 1)) (G : Fin 7 ↪ Fin nr)

theorem skip_step {P : WM ns nr} {m : ℕ} (A u : List Bool)
    (h : WExec cap P (σ.seth IN (marks A).length)
      ((σ.seth IN (marks A).length).seth IN ((marks A).length + stp true * u.length)) m) :
    WExec cap P (σ.seth IN (marks A).length) (σ.seth IN (marks (A ++ u)).length) m := by
  refine WExec.cast cap h ?_ le_rfl
  rw [seth_seth]; congr 1; simp [marks_length, stp]

/-- **Reading `S`.** From the head at the start of `frame` of `true :: callWord c ++ natWords xs ++ natWord S ++ …`
(nineteen numbers `xs`), with the seven registers at zero, `readS` puts `S` in register `G 6` and leaves the head
just past `natWord S`; nothing else changes. -/
theorem readS_exec {m : ℕ} (c : Call) (xs : List ℕ) (S : ℕ) (rest restIN : List Bool)
    (hIN : σ.st IN = marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S ++
      rest) ++ restIN)
    (hINh : σ.sh IN = 0) (hz : ∀ i, σ.val (G i) = 0) (hfit : ReadFits cap c xs S) (hxs : xs.length = m) :
    WExec cap (readS IN G m) σ
      ((σ.seth IN (marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++
        natWord S)).length).setv (G 6) S) (readCost c xs S) := by
  have hne : ∀ {a b : Fin 7}, a ≠ b → G a ≠ G b := fun h => G.injective.ne h
  have hd6 : [G 0, G 1, G 2, G 3, G 4, G 5].Nodup := by
    simp
  have hd5 : [G 0, G 1, G 2, G 4, G 5].Nodup := by
    simp
  have hzs : ∀ m, NearCubicGates.Close.Codec.Zeros (σ.seth IN m) [G 0, G 1, G 2, G 3, G 4, G 5] := by
    intro m r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hz _
  set u1 := natWord c.n with hu1
  set u2 := natWord (kindTag c.kind) with hu2
  set u3 := circuitWord c.first with hu3
  set u4 := circuitWord c.second with hu4
  set u5 := listWord natWord c.parity with hu5
  set u6 := NearCubicGates.Close.Interfaces.intWord c.radius.num with hu6
  set u7 := natWord c.radius.den with hu7
  set u8 := xs.flatMap natWord with hu8
  set u9 := natWord S with hu9
  have hW : [true] ++ NearCubicGates.Close.Interfaces.callWord c ++ u8 ++ u9 ++ rest =
      [true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest := by
    rw [callWord_split]; simp only [List.append_assoc]; rfl
  have hIN' : σ.st IN = marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest) ++ restIN := by
    rw [hIN, hW]
  have hseg : ∀ (A u B : List Bool), A ++ u ++ B = [true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest →
      ∀ m, (σ.seth IN m).st IN = marks A ++ enc true u ++ (marks B ++ restIN) := by
    intro A u B h m
    simp only [WState.seth_st]
    rw [hIN', ← h]
    simp only [enc_true, marks_append, List.append_assoc]
  -- the tag
  have a1 : WExec cap (.fwd IN) σ (σ.seth IN 1) 1 := by
    have := WExec.fwd (cap := cap) IN σ
    rwa [hINh] at this
  have a2 : WExec cap (.fwd IN) (σ.seth IN 1) (σ.seth IN (marks [true]).length) 1 := by
    have := WExec.fwd (cap := cap) IN (σ.seth IN 1)
    refine WExec.cast cap this ?_ le_rfl
    rw [seth_seth]; congr 1; simp [marks]
  -- the call word
  have e1 := skip_step cap σ IN [true] u1 (NearCubicGates.Close.Codec.skipNat_spec cap true IN (G 0) (G 1)
    (hne (by decide)) c.n (marks [true]) _ (σ.seth IN (marks [true]).length)
    (hseg [true] u1 (u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _)
    (by simp) (hz 0) (hz 1) hfit.n)
  have e2 := skip_step cap σ IN ([true] ++ u1) u2 (NearCubicGates.Close.Codec.skipNat_spec cap true IN (G 0) (G 1)
    (hne (by decide)) (kindTag c.kind) (marks ([true] ++ u1)) _ (σ.seth IN (marks ([true] ++ u1)).length)
    (hseg _ u2 (u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _)
    (by simp) (hz 0) (hz 1) hfit.kind)
  have e3 := skip_step cap σ IN ([true] ++ u1 ++ u2) u3 (NearCubicGates.Close.Codec.skipCircuit_spec cap true IN
    (G 0) (G 1) (G 2) (G 3) (G 4) (G 5) hd6 c.first hfit.first (marks ([true] ++ u1 ++ u2)) _
    (σ.seth IN (marks ([true] ++ u1 ++ u2)).length)
    (hseg _ u3 (u4 ++ u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _) (by simp) (hzs _))
  have e4 := skip_step cap σ IN ([true] ++ u1 ++ u2 ++ u3) u4 (NearCubicGates.Close.Codec.skipCircuit_spec cap true IN
    (G 0) (G 1) (G 2) (G 3) (G 4) (G 5) hd6 c.second hfit.second (marks ([true] ++ u1 ++ u2 ++ u3)) _
    (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3)).length)
    (hseg _ u4 (u5 ++ u6 ++ u7 ++ u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _) (by simp) (hzs _))
  have e5 := skip_step cap σ IN ([true] ++ u1 ++ u2 ++ u3 ++ u4) u5 (NearCubicGates.Close.Codec.skipList_spec cap
    true IN (G 0) (G 1) (G 2) (G 4) (G 5) (NearCubicGates.Close.Codec.skipNat true IN (G 0) (G 1)) hd5 natWord
    (fun x => 20 * natBitLength x + 20) (fun τ => τ.val (G 0) = 0 ∧ τ.val (G 1) = 0)
    (fun τ x h => h) (fun τ x h => ⟨by simp [Function.update_of_ne (hne (show (0 : Fin 7) ≠ 2 by decide)), h.1],
      by simp [Function.update_of_ne (hne (show (1 : Fin 7) ≠ 2 by decide)), h.2]⟩) c.parity
    (fun x hx pre rest' τ hτ hst hsh => NearCubicGates.Close.Codec.skipNat_spec cap true IN (G 0) (G 1)
      (hne (by decide)) x pre rest' τ hst hsh hτ.1 hτ.2 (hfit.par x hx))
    (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4)) _ (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4)).length)
    ⟨hz 0, hz 1⟩ (hseg _ u5 (u6 ++ u7 ++ u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _) (by simp)
    (hz 0) (hz 1) (hz 2) (hz 4) (hz 5) hfit.parLen hfit.parLen')
  have e6 := skip_step cap σ IN ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5) u6
    (NearCubicGates.Close.Codec.skipInt_spec cap true IN (G 0) (G 1) (hne (by decide)) c.radius.num
    (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5)) _ (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5)).length)
    (hseg _ u6 (u7 ++ u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _) (by simp) (hz 0) (hz 1) hfit.num)
  have e7 := skip_step cap σ IN ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6) u7
    (NearCubicGates.Close.Codec.skipNat_spec cap true IN (G 0) (G 1) (hne (by decide)) c.radius.den
    (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6)) _
    (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6)).length)
    (hseg _ u7 (u8 ++ u9 ++ rest) (by simp [List.append_assoc]) _) (by simp) (hz 0) (hz 1) hfit.den)
  -- the nineteen parameters
  have e8 : WExec cap (skipNats IN (G 0) (G 1) m)
      (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7)).length)
      (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8)).length) (natsCost xs) := by
    have := skipNats_exec cap IN (G 0) (G 1) (hne (by decide)) xs (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++
      u6 ++ u7)) (marks (u9 ++ rest) ++ restIN) (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++
      u7)).length) (by rw [← enc_true]; exact hseg _ u8 (u9 ++ rest) (by simp [List.append_assoc]) _)
      (by simp) (hz 0) (hz 1) hfit.params
    rw [hxs, seth_seth, ← hu8] at this
    refine WExec.cast cap this ?_ le_rfl
    congr 1; simp [marks_length]; ring
  -- `S`
  have e9 := readNatM_spec cap true IN (G 0) (G 1) (G 6) (G 4) (G 5) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) S (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8))
    (marks rest ++ restIN) (σ.seth IN (marks ([true] ++ u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6 ++ u7 ++ u8)).length)
    (hseg _ u9 rest (by simp [List.append_assoc]) _) (by simp) (hz 0) (hz 1) (hz 4) (hz 5)
    (by simp [hz 6]; exact hfit.rounds)
  refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 e9)))))))))) ?_ ?_
  · rw [seth_seth]
    simp only [WState.seth_val, hz 6, Nat.zero_add]
    congr 2
    simp only [hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9]
    rw [callWord_split]; simp [marks_length, stp]; ring
  · unfold readCost; omega

end ReadS

end NearQuarticWires.Control
