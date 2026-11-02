import Proof.Quartic.StageMain.Circuit
import Proof.Quartic.StageOutput.Codec

/-!
# The encoded-circuit evaluation program

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. A single program reads the packed point
and the literal circuit word and writes its Boolean value. The point,
weights, top coefficients and top table are all supplied on the input tape.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

structure CircuitRequest where
  n : ℕ
  circuit : NCircuit n
  point : ℕ

def CircuitRequest.word (r : CircuitRequest) : List Bool := natWord r.point ++ circuitWord r.circuit
def CircuitRequest.value (r : CircuitRequest) : Bool := r.circuit.eval (packedPoint r.n r.point)

def emitCircuit : St VV := .ite (.eq tableResult v1) (.op (.emit true)) (.op (.emit false))

theorem emitCircuit_spec {C : Ctx} (a : DS VV) (hc : Cst a) (bit : Bool)
    (hbit : a.env tableResult = bit.toNat) :
    Hs C emitCircuit a 2 (fun b => b.out = a.out ++ [bit]) := by
  cases bit with
  | false =>
    have he : (Cnd.eq tableResult v1).eval a = false := by simp [Cnd.eval, hbit, hc.one]
    refine Hs.mono (Hs.iteF (show tableResult ≠ v1 by decide) he (hs_emit C false a)) le_rfl ?_
    rintro b rfl
    rfl
  | true =>
    have he : (Cnd.eq tableResult v1).eval a = true := by simp [Cnd.eval, hbit, hc.one]
    refine Hs.mono (Hs.iteT (show tableResult ≠ v1 by decide) he (hs_emit C true a)) le_rfl ?_
    rintro b rfl
    rfl

def circuitProgram : St VV := .seq StageOutput.constants
  (.seq readNat (.seq (.op (.copy pointSaved t3)) (.seq scoreCircuit emitCircuit)))

def circuitSteps (L : ℕ) : ℕ := 1000 * (L + 4) ^ 3

theorem circuitProgram_spec {C : Ctx} (r : CircuitRequest)
    (hin : C.cw = r.word) (hW : C.cw.length + 4 ≤ C.Wd) :
    Hs C circuitProgram a0 (circuitSteps C.cw.length) (fun b => b.out = [r.value]) := by
  have hlen : (natWord r.point).length ≤ C.cw.length := by rw [hin]; simp [CircuitRequest.word]
  have hnb := natBitLength_le_len r.point
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (StageOutput.constants_spec (C := C) (by omega))
    (fun a ⟨ac, ap, _, ao⟩ n1 hn1 => ?_))
  have ai : C.cw.drop a.cp = natWord r.point ++ circuitWord r.circuit := by rw [ap, List.drop_zero, hin]; rfl
  refine Hs.then (readNat_spec a ac r.point _ ai (by omega) hL)
    (fun b ⟨bv, _, bp, _, bo, bc, _⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C pointSaved t3 b (by decide)) (fun d hd n3 hn3 => ?_)
  subst hd
  let d := b.set pointSaved (b.env t3)
  have dc : Cst d := bc.set _ _ (by decide)
  have dp : d.env pointSaved = r.point := by simp [d, bv]
  have di : C.cw.drop d.cp = circuitWord r.circuit ++ [] := by
    simp only [d, DS.set_cp, bp, drop_adv ai, List.append_nil]
  have dpoint : d.env pointSaved < 2 ^ C.Wd := by
    rw [dp]
    exact (lt_natBitLength r.point).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine Hs.then (scoreCircuit_spec r.circuit d dc [] di hW dpoint)
    (fun e ⟨ev, _, _, eo, ec, _⟩ n4 hn4 => ?_)
  refine Hs.last (emitCircuit_spec e ec r.value (by simpa only [dp, CircuitRequest.value] using ev)) ?_
  rintro f fo n5 hn5
  refine ⟨?_, ?_⟩
  · rw [fo, eo]
    simp only [d, DS.set_out, bo, ao, List.nil_append]
  · unfold circuitSteps
    nlinarith only [hn1, hn2, hn3, hn4, hn5, hnb, hlen]

end NearQuarticWires.StageMain
