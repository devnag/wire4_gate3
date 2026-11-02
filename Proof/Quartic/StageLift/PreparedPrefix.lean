import Proof.Quartic.StageLift.ParameterMeasure
import Proof.Quartic.StageLift.PrintFrames
import Proof.Quartic.StageMain.CallSkipTagged

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain.CallSkip

/-- `sec:algorithm`, paper/paper.tex: the common
source prefix ends immediately before the actual witness frame. -/
def preparedPrefixWord (c : Call) (p : Cells.Parameters) : List Bool :=
  true :: (callWord c ++ Program.parametersWord p)

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the witness address is computed by physically reading
the call and parameter codecs, including their list-length headers. -/
def scanPreparedPrefix : St VV MM :=
  .seq scanTaggedCall (.seq scanParameters (.op (.inc lengthCounter)))

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the complete actual source prefix is consumed and its
literal length is retained in a runtime register. No following witness,
certificate, Gamma-table or table-index bits enter its allocation bound. -/
theorem scanPreparedPrefix_spec (C : Ctx) (c : Call) (p : Cells.Parameters)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = preparedPrefixWord c p ++ rest)
    (hwidth : (preparedPrefixWord c p).length + 2 ≤ C.Wd) :
    Hs C scanPreparedPrefix a
      (3000 * ((callWord c).length + 1) ^ 3 +
        4000 * ((Program.parametersWord p).length + 1) ^ 2 + 7) (fun b =>
      b.ip = a.ip + (preparedPrefixWord c p).length ∧
      b.env lengthCounter = (preparedPrefixWord c p).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b gateListScratch) := by
  have hlen : (preparedPrefixWord c p).length =
      1 + (callWord c).length + (Program.parametersWord p).length := by
    simp [preparedPrefixWord, Nat.add_comm, Nat.add_left_comm]
  have hprefix : C.inp.drop a.ip = true ::
      (callWord c ++ (Program.parametersWord p ++ rest)) := by
    simpa only [preparedPrefixWord, List.cons_append, List.append_assoc] using hin
  have he := scanTaggedCall_run C c (Program.parametersWord p ++ rest) a hc hprefix
    (by rw [hlen] at hwidth; omega)
  unfold scanPreparedPrefix
  refine (Hs.seq (t1 := 3000 * ((callWord c).length + 1) ^ 3 + 4)
    (t2 := 4000 * ((Program.parametersWord p).length + 1) ^ 2 + 2) he
    fun b ⟨hbi, hbl, hbrest, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = Program.parametersWord p ++ rest := by
    rw [hbi, show a.ip + 1 + (callWord c).length = a.ip + ((callWord c).length + 1) by omega,
      ← List.drop_drop, hprefix]
    simp only [List.drop_succ_cons, List.drop_left]
  have hbcap : b.env lengthCounter + (Program.parametersWord p).length < 2 ^ C.Wd := by
    rw [hbl]
    have hx : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    rw [hlen] at hwidth
    omega
  have ep := scanParameters_spec C (Program.parametersWord p).length b hbc p rest
    hbin le_rfl (by rw [hlen] at hwidth; omega) hbcap
  refine Hs.seq (t2 := 1) ep fun d hd => ?_
  have hdlen : d.env lengthCounter + 1 = (preparedPrefixWord c p).length := by
    rw [hd.bytes, hbl, hlen]
    omega
  refine (hs_inc C lengthCounter d (by
    rw [hdlen]
    have hx : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    omega)).mono le_rfl ?_
  rintro e rfl
  refine ⟨?_, hdlen, ?_, ?_, ?_⟩
  · change d.ip = _
    rw [hd.pos, hbi, hlen]
    omega
  · exact hd.unchanged.trans hbrest
  · exact Cst.of_fr hd.constants (Fr.set (T := [lengthCounter]) d _ (by simp)) (by decide)
  · exact hbf.trans ((hd.registers.weaken scalarScratch_in_gate).trans
      (Fr.set _ _ (by decide)))

/-- Step 3, `sec:algorithm`, paper/paper.tex: the real printer
request has exactly the successful shared prefix followed by the witness,
Gamma-table and table-index words, with no certification bits. -/
theorem printInput_preparedPrefix {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    Greedy.printInput r = preparedPrefixWord r.child.call r.child.selected.1 ++
      frame (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness) ++
      Greedy.gammaTableWord r.child ++ Greedy.printIndexWord r := by
  rw [printInput_layout]
  simp only [preparedPrefixWord, Greedy.gammaTableWord, List.cons_append, List.append_assoc]

end NearQuarticWires.StageLift
