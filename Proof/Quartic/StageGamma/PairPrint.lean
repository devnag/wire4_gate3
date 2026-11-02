import Proof.Quartic.StageGamma.PairAccumulator
import Proof.Quartic.StageCert.OutputRadix

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `cor:conditional`, paper/paper.tex: the exact
absolute numerator is formed in an independent binary output variable. -/
def gammaPrintMagnitude : Fin VV := ⟨105, by decide⟩

/-- `cor:conditional`, paper/paper.tex: after its
sign bit is selected, the original numerator's magnitude is physically
formed by ordered subtraction and emitted as a canonical natural. -/
def printPairMagnitude (larger smaller : Fin VV) : St VV MM :=
  .seq (.op (.copy gammaPrintMagnitude larger))
    (.seq (.op (.sub gammaPrintMagnitude smaller))
      (StageCert.emitOutputNat gammaPrintMagnitude))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: actual binary subtraction followed by canonical bit emission
prints the exact magnitude, paying its true binary output length. -/
theorem printPairMagnitude_run (C : Ctx) (larger smaller : Fin VV)
    (hlarge : larger ≠ gammaPrintMagnitude) (hsmall : smaller ≠ gammaPrintMagnitude)
    (a : DS VV MM) (hc : Cst a) (p n : ℕ)
    (hp : a.env larger = p) (hn : a.env smaller = n) (horder : n ≤ p)
    (hfit : p - n < 2 ^ C.Wd) (hwidth : 3 ≤ C.Wd) :
    Hs C (printPairMagnitude larger smaller) a (40 * natBitLength (p - n) + 46)
      (fun b => b.out = a.out ++ natWord (p - n)) := by
  unfold printPairMagnitude
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * natBitLength (p - n) + 44)
    (hs_copy C gammaPrintMagnitude larger a hlarge.symm) ?_) (by omega) (fun _ h => h)
  intro b hb
  subst hb
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 40 * natBitLength (p - n) + 42)
    (hs_sub C gammaPrintMagnitude smaller _ hsmall.symm
      (by rw [DS.set_env_ne _ _ hsmall, DS.set_env_self, hp, hn]; exact horder)) ?_)
    (by omega) (fun _ h => h)
  intro b hb
  subst hb
  let b := (a.set gammaPrintMagnitude (a.env larger)).set gammaPrintMagnitude
    ((a.set gammaPrintMagnitude (a.env larger)).env gammaPrintMagnitude -
      (a.set gammaPrintMagnitude (a.env larger)).env smaller)
  have bmag : b.env gammaPrintMagnitude = p - n := by simp [b, hsmall, hp, hn]
  have bc : Cst b := by
    exact Cst.of_fr (T := [gammaPrintMagnitude]) hc
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide)
  refine Hs.mono (StageCert.emitOutputNat_run C gammaPrintMagnitude (by decide) b bc hwidth
    (p - n) bmag hfit) le_rfl ?_
  intro e ⟨he, _, _, _⟩
  exact he

/-- `cor:conditional`, paper/paper.tex: one actual
comparison selects the signed ORIGINAL numerator's canonical integer codec. -/
def printPair : St VV MM :=
  .ite (.lt gammaPositiveSum gammaNegativeSum)
    (.seq (StageCert.emitOutputNat v1) (printPairMagnitude gammaNegativeSum gammaPositiveSum))
    (.seq (StageCert.emitOutputNat vZ) (printPairMagnitude gammaPositiveSum gammaNegativeSum))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the complete signed accumulator is printed byte-exactly as
the required canonical integer word, including zero and inclusive equality. -/
theorem printPair_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (p n : ℕ)
    (hp : a.env gammaPositiveSum = p) (hn : a.env gammaNegativeSum = n)
    (hpf : p < 2 ^ C.Wd) (hnf : n < 2 ^ C.Wd) (hwidth : 3 ≤ C.Wd) :
    Hs C printPair a (40 * C.Wd + 130) (fun b =>
      b.out = a.out ++ NearCubicGates.Close.Interfaces.intWord ((p : ℤ) - n)) := by
  have hd : (p - n < 2 ^ C.Wd) ∧ (n - p < 2 ^ C.Wd) :=
    ⟨(Nat.sub_le _ _).trans_lt hpf, (Nat.sub_le _ _).trans_lt hnf⟩
  have hprint : ∀ (neg : Bool) (larger smaller : Fin VV) (P N : ℕ),
      larger ≠ gammaPrintMagnitude → smaller ≠ gammaPrintMagnitude →
      a.env larger = P → a.env smaller = N → N ≤ P → P - N < 2 ^ C.Wd →
      larger ∉ emT → smaller ∉ emT →
      Hs C (.seq (StageCert.emitOutputNat (if neg then v1 else vZ))
        (printPairMagnitude larger smaller)) a (40 * C.Wd + 129)
        (fun b => b.out = a.out ++ natWord neg.toNat ++ natWord (P - N)) := by
    intro neg larger smaller P N hl hs hP hN horder hfit hlt hst
    have hsign : a.env (if neg then v1 else vZ) = neg.toNat := by
      cases neg <;> simp [hc.z, hc.one]
    have hsignfit : neg.toNat < 2 ^ C.Wd := by
      cases neg
      · exact Nat.two_pow_pos _
      · exact Nat.one_lt_two_pow (by omega)
    have hb : natBitLength (P - N) ≤ C.Wd :=
      natBitLength_le_of_lt _ _ (by omega) hfit
    refine Hs.mono (Hs.seq (t1 := 82) (t2 := 40 * natBitLength (P - N) + 46)
      (Hs.mono (StageCert.emitOutputNat_run C (if neg then v1 else vZ)
        (by cases neg <;> decide) a hc hwidth neg.toNat hsign hsignfit)
        (by cases neg <;> norm_num [natBitLength]) (fun _ h => h)) ?_)
      (by omega) (fun _ h => h)
    intro b ⟨bo, _, bc, bf⟩
    refine Hs.mono (printPairMagnitude_run C larger smaller hl hs b bc P N
      (by rw [bf larger hlt]; exact hP) (by rw [bf smaller hst]; exact hN) horder hfit hwidth)
      le_rfl ?_
    intro e he
    rw [he, bo, List.append_assoc]
  unfold printPair
  refine Hs.ite (c := .lt gammaPositiveSum gammaNegativeSum) (t := 40 * C.Wd + 129)
    (by change gammaPositiveSum ≠ gammaNegativeSum; decide) ?_ ?_
  · intro he
    have hlt : p < n := by simpa [Cnd.eval, hp, hn] using he
    refine Hs.mono (hprint true gammaNegativeSum gammaPositiveSum n p
      (by decide) (by decide) hn hp (by omega) hd.2 (by decide) (by decide)) le_rfl ?_
    intro b hb
    have hz : (p : ℤ) - n < 0 := by omega
    simpa [NearCubicGates.Close.Interfaces.intWord, hz, Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ n),
      List.append_assoc] using hb
  · intro he
    have hle : n ≤ p := by
      have hh : ¬p < n := by simpa [Cnd.eval, hp, hn] using he
      omega
    refine Hs.mono (hprint false gammaPositiveSum gammaNegativeSum p n
      (by decide) (by decide) hp hn hle hd.1 (by decide) (by decide)) le_rfl ?_
    intro b hb
    have hz : ¬(p : ℤ) - n < 0 := by omega
    simpa [NearCubicGates.Close.Interfaces.intWord, hz, Int.natAbs_natCast_sub_natCast_of_ge hle, List.append_assoc] using hb

end NearQuarticWires.StageGamma
