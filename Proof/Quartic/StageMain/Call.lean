import Proof.Quartic.StageMain.Circuit
import Proof.Quartic.StageMain.Parity
import Proof.Quartic.StageMain.CallChoose
import Proof.Quartic.StageMain.CallTail

/-!
# Evaluating the predicate of a literal counting call

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The program parses the call header, both
encoded circuits, the parity-index list, and the radius. It returns the
exact single, pair, or parity predicate at the retained packed input.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def scoreCall : St VV := .seq callHeader
  (.seq scoreCircuit (.seq (.op (.copy firstValue tableResult))
    (.seq scoreCircuit (.seq (.op (.copy secondValue tableResult))
      (.seq evalParity (.seq skipRadius callChoose))))))
def scoreCallScratch : List (Fin VV) := callHeaderScratch ++ [firstValue, secondValue] ++
  scoreCircuitScratch ++ evalParityScratch ++ readNatT ++ [tableResult]

theorem scoreCall_spec {C : Ctx} (c : Call) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp = callWord c ++ rest)
    (hW : C.cw.length + 4 ≤ C.Wd) (hn : c.n ≤ C.cw.length)
    (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C scoreCall a (3000 * (C.cw.length + 2) ^ 3) (fun b =>
      b.env tableResult = (c.predicate (packedPoint c.n (a.env pointSaved))).toNat ∧
      b.cp = a.cp + (callWord c).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b scoreCallScratch) := by
  have hi : C.cw.drop a.cp = natWord c.n ++ (natWord (kindTag c.kind) ++
      (circuitWord c.first ++ (circuitWord c.second ++
        (listWord natWord c.parity ++ (ratWord c.radius ++ rest))))) := by
    simpa only [callWord, List.append_assoc] using hin
  have hl := len_le_of_drop hin
  have hb0 := natBitLength_le_len c.n
  have hb1 := natBitLength_le_len (kindTag c.kind)
  simp only [callWord, List.length_append] at hl
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (callHeader_spec a hc c.n _ _ hi (by omega) (by omega) hL)
    (fun b ⟨bn, bk, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bi : C.cw.drop b.cp = circuitWord c.first ++ (circuitWord c.second ++
      (listWord natWord c.parity ++ (ratWord c.radius ++ rest))) := by
    rw [bp, ← List.drop_drop, ← List.drop_drop, hi, List.drop_left, List.drop_left]
  have bx : b.env pointSaved = a.env pointSaved := bf _ (by decide)
  refine Hs.then (scoreCircuit_spec c.first b bc _ bi hW (by rw [bx]; exact hpoint))
    (fun d ⟨dv, dp, dw, dout, dc, df⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C firstValue tableResult d (by decide)) (fun e he n3 hn3 => ?_)
  subst he
  let e := d.set firstValue (d.env tableResult)
  have ec : Cst e := dc.set _ _ (by decide)
  have ex : e.env pointSaved = a.env pointSaved := by
    simp only [e, DS.set_env_ne _ _ (show pointSaved ≠ firstValue by decide)]
    exact (df _ (by decide) (by decide)).trans bx
  have ei : C.cw.drop e.cp = circuitWord c.second ++
      (listWord natWord c.parity ++ (ratWord c.radius ++ rest)) := by
    simp only [e, DS.set_cp, dp, drop_adv bi]
  refine Hs.then (scoreCircuit_spec c.second e ec _ ei hW (by rw [ex]; exact hpoint))
    (fun f ⟨fv, fp, fw, fo, fc, ff⟩ n4 hn4 => ?_)
  refine Hs.then (hs_copy C secondValue tableResult f (by decide)) (fun g hg n5 hn5 => ?_)
  subst hg
  let g := f.set secondValue (f.env tableResult)
  have gc : Cst g := fc.set _ _ (by decide)
  have gx : g.env pointSaved = a.env pointSaved := by
    simp only [g, DS.set_env_ne _ _ (show pointSaved ≠ secondValue by decide)]
    exact (ff _ (by decide) (by decide)).trans ex
  have gn : g.env callArity = c.n := by
    simp only [g, DS.set_env_ne _ _ (show callArity ≠ secondValue by decide)]
    rw [ff _ (by decide) (by decide)]
    simp only [e, DS.set_env_ne _ _ (show callArity ≠ firstValue by decide)]
    exact (df _ (by decide) (by decide)).trans bn
  have gi : C.cw.drop g.cp = listWord natWord c.parity ++ (ratWord c.radius ++ rest) := by
    simp only [g, DS.set_cp, fp, drop_adv ei]
  refine Hs.then (evalParity_spec c.parity _ g gc gi (by omega) (by rw [gn]; omega)
    (by rw [gx]; exact hpoint))
    (fun h ⟨hv, hp, hw, ho, hc', hf⟩ n6 hn6 => ?_)
  have hinput : C.cw.drop h.cp = ratWord c.radius ++ rest := by rw [hp, drop_adv gi]
  refine Hs.then (skipRadius_spec h hc' c.radius rest hinput (by omega) hL)
    (fun j ⟨jp, jw, jo, jc, jf⟩ n7 hn7 => ?_)
  have jkind : j.env callKind = kindTag c.kind := by
    rw [jf _ (by decide), hf _ (by decide) (by decide)]
    simp only [g, DS.set_env_ne _ _ (show callKind ≠ secondValue by decide)]
    rw [ff _ (by decide) (by decide)]
    simp only [e, DS.set_env_ne _ _ (show callKind ≠ firstValue by decide)]
    exact (df _ (by decide) (by decide)).trans bk
  have jfirst : j.env firstValue = (c.first.eval (packedPoint c.n (a.env pointSaved))).toNat := by
    rw [jf _ (by decide), hf _ (by decide) (by decide)]
    simp only [g, DS.set_env_ne _ _ (show firstValue ≠ secondValue by decide)]
    rw [ff _ (by decide) (by decide)]
    simp only [e, DS.set_env_self, dv, bx]
  have jsecond : j.env secondValue = (c.second.eval (packedPoint c.n (a.env pointSaved))).toNat := by
    rw [jf _ (by decide), hf _ (by decide) (by decide)]
    simp only [g, DS.set_env_self, fv, ex]
  have jpar : j.env parityResult = (c.parityOf (packedPoint c.n (a.env pointSaved))).toNat := by
    rw [jf _ (by decide), hv, gn, gx, parityFold_eq]
  refine Hs.last (callChoose_spec j jc c.kind _ _ _ jkind jfirst jsecond jpar) ?_
  rintro z ⟨zv, zp, zw, zo, zc, zf⟩ n8 hn8
  refine ⟨⟨?_, ?_, ?_, ?_, zc, ?_⟩, ?_⟩
  · cases hk : c.kind <;> simpa only [callChoice, Call.predicate, hk] using zv
  · rw [zp, jp, hp]
    simp only [g, DS.set_cp, fp, e, dp, bp]
    simp only [callWord, List.length_append, Nat.add_assoc]
  · rw [zw, jw, hw]
    simp only [g, DS.set_wq, fw, e, dw, bw]
  · rw [zo, jo, ho]
    simp only [g, DS.set_out, fo, e, dout, bo]
  · exact FrS.trans (bf.toS.weaken (by decide))
      (FrS.trans (df.weaken (by decide)) (FrS.trans (Fr.set _ _ (by decide)).toS
        (FrS.trans (ff.weaken (by decide)) (FrS.trans (Fr.set _ _ (by decide)).toS
          (FrS.trans (hf.weaken (by decide)) (FrS.trans (jf.toS.weaken (by decide))
            (zf.toS.weaken (by decide))))))))
  · rw [gn] at hn6
    have hn6' : n6 ≤ 800 * (C.cw.length + 2) ^ 2 := by
      have hh := Nat.pow_le_pow_left (show C.cw.length + c.n + 2 ≤ 2 * (C.cw.length + 2) by omega) 2
      nlinarith only [hn6, hh]
    nlinarith only [hn1, hn2, hn3, hn4, hn5, hn6', hn7, hn8, hb0, hb1, hl]

end NearQuarticWires.StageMain
