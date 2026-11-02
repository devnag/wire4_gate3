import Proof.Quartic.StageMain.Call
import Proof.Quartic.StageMain.CircuitProgram

/-!
# The encoded-call predicate program

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. A single program reads the packed point
and the literal call word and writes its predicate bit. The call arity is
bounded by the input length, as for dispatched nonzero-wire calls. All
circuit, parity, kind, and radius fields are read from the actual tape.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

structure PredicateRequest where
  call : Call
  point : ℕ
  arity_le_word : call.n ≤ (natWord point ++ callWord call).length

def PredicateRequest.word (r : PredicateRequest) : List Bool := natWord r.point ++ callWord r.call
def PredicateRequest.value (r : PredicateRequest) : Bool := r.call.predicate (packedPoint r.call.n r.point)

def predicateProgram : St VV := .seq StageOutput.constants
  (.seq readNat (.seq (.op (.copy pointSaved t3)) (.seq scoreCall emitCircuit)))

def predicateSteps (L : ℕ) : ℕ := 4000 * (L + 4) ^ 3

theorem predicateProgram_spec {C : Ctx} (r : PredicateRequest)
    (hin : C.cw = r.word) (hW : C.cw.length + 4 ≤ C.Wd) :
    Hs C predicateProgram a0 (predicateSteps C.cw.length) (fun b => b.out = [r.value]) := by
  have hlen : (natWord r.point).length ≤ C.cw.length := by rw [hin]; simp [PredicateRequest.word]
  have hnb := natBitLength_le_len r.point
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (StageOutput.constants_spec (C := C) (by omega))
    (fun a ⟨ac, ap, _, ao⟩ n1 hn1 => ?_))
  have ai : C.cw.drop a.cp = natWord r.point ++ callWord r.call := by rw [ap, List.drop_zero, hin]; rfl
  refine Hs.then (readNat_spec a ac r.point _ ai (by omega) hL)
    (fun b ⟨bv, _, bp, _, bo, bc, _⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C pointSaved t3 b (by decide)) (fun d hd n3 hn3 => ?_)
  subst hd
  let d := b.set pointSaved (b.env t3)
  have dc : Cst d := bc.set _ _ (by decide)
  have dp : d.env pointSaved = r.point := by simp [d, bv]
  have di : C.cw.drop d.cp = callWord r.call ++ [] := by
    simp only [d, DS.set_cp, bp, drop_adv ai, List.append_nil]
  have dpoint : d.env pointSaved < 2 ^ C.Wd := by
    rw [dp]
    exact (lt_natBitLength r.point).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  refine Hs.then (scoreCall_spec r.call d dc [] di hW (by rw [hin]; exact r.arity_le_word) dpoint)
    (fun e ⟨ev, _, _, eo, ec, _⟩ n4 hn4 => ?_)
  refine Hs.last (emitCircuit_spec e ec r.value (by simpa only [dp, PredicateRequest.value] using ev)) ?_
  rintro f fo n5 hn5
  refine ⟨?_, ?_⟩
  · rw [fo, eo]
    simp only [d, DS.set_out, bo, ao, List.nil_append]
  · unfold predicateSteps
    nlinarith only [hn1, hn2, hn3, hn4, hn5, hnb, hlen]

end NearQuarticWires.StageMain
