import Proof.Quartic.StageMain.CallSkipCircuit

/-!
# The exact measured original-call scanner

`prop:time`, paper/paper.tex: the original call's
arity, kind, two threshold circuits, parity list and rational radius
are read in their literal order. The runtime length counter excludes
every following parameter, witness, certificate and table bit.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

def skipCall : St VV MM := .seq scanNat (.seq scanNat (.seq skipCircuit
  (.seq skipCircuit (.seq skipNatList skipRat))))

theorem skipCall_spec : ScanSpec skipCall callWord gateListScratch
    (fun L => 3000 * (L + 1) ^ 3) := by
  have hfirst : ScanSpec skipCircuit (fun c : Call => circuitWord c.first) gateListScratch
      (fun L => 1000 * (L + 1) ^ 3) := by
    intro C L a hc c rest hin hlen hW hcap
    exact skipCircuit_spec C L a hc c.first rest hin hlen hW hcap
  have hsecond : ScanSpec skipCircuit (fun c : Call => circuitWord c.second) gateListScratch
      (fun L => 1000 * (L + 1) ^ 3) := by
    intro C L a hc c rest hin hlen hW hcap
    exact skipCircuit_spec C L a hc c.second rest hin hlen hW hcap
  have h := (scanNat_spec.map Call.n).seq ((scanNat_spec.map (fun c : Call => kindTag c.kind)).seq
    (hfirst.seq (hsecond.seq ((skipNatList_spec.map Call.parity).seq (skipRat_spec.map Call.radius)))))
  have heq : (fun c : Call => natWord c.n ++ (natWord (kindTag c.kind) ++
      (circuitWord c.first ++ (circuitWord c.second ++
        (listWord natWord c.parity ++ ratWord c.radius))))) = callWord := by
    funext c
    simp only [callWord, List.append_assoc]
  rw [heq] at h
  refine h.weaken ?_ (by
    intro L
    have hpow : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    have hpos : 0 < (L + 1) ^ 3 := by positivity
    nlinarith only [hpow, hpos])
  intro x hx
  have ha : x ∈ atomScratch → x ∈ gateListScratch := fun hx =>
    scalarScratch_in_gate x (List.mem_append_left _ hx)
  simp only [List.mem_append] at hx
  rcases hx with hx | hx | hx | hx | hx | hx
  · exact ha hx
  · exact ha hx
  · exact hx
  · exact hx
  · exact scalarScratch_in_gate x hx
  · exact ha hx

def scanCall : St VV MM := .seq (.op (.zero lengthCounter)) skipCall

theorem scanCall_run (C : Ctx) (c : Call) (rest : List Bool) (a : DS VV MM)
    (hc : Cst a) (hin : C.inp.drop a.ip = callWord c ++ rest)
    (hW : (callWord c).length + 2 ≤ C.Wd) :
    Hs C scanCall a (3000 * ((callWord c).length + 1) ^ 3 + 2) (fun b =>
      b.ip = a.ip + (callWord c).length ∧
      b.env lengthCounter = (callWord c).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b gateListScratch) := by
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 3000 * ((callWord c).length + 1) ^ 3)
    (hs_zero C lengthCounter a) ?_) (by omega) (fun _ h => h)
  rintro b rfl
  have hf : Fr a (a.set lengthCounter 0) gateListScratch := Fr.set a _ (by decide)
  have hbc := Cst.of_fr hc hf (by decide)
  refine (skipCall_spec C (callWord c).length _ hbc c rest hin le_rfl hW
    (by simp only [DS.set_env_self, Nat.zero_add]; exact lt_trans (by omega) Nat.lt_two_pow_self)).mono le_rfl ?_
  intro d hd
  exact ⟨hd.pos, by simpa using hd.bytes, hd.unchanged, hd.constants, hf.trans hd.registers⟩

end NearQuarticWires.StageMain.CallSkip
