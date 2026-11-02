import Proof.Quartic.StageOutput.Padding

/-!
# Copying the Step 5 fields and allocating arithmetic width

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The program parses all thirteen scalar fields, writes the
identical tagged word, and appends one padding bit for each input variable.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

def Input.padded (d : Input) : List Bool := true :: (d.word ++ List.replicate d.n false)

def truePaddingBody : St VV :=
  .seq parseInput (.seq (.op (.emit true)) (.seq (printVars inputVariables) appendPadding))

theorem truePaddingBody_spec {C : Ctx} (d : Input)
    (hW : ∀ xv ∈ d.fields, natBitLength xv.2 + 2 ≤ C.Wd)
    (hW3 : 3 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (a : DS VV) (hc : Cst a) (hv : Valid C a)
    (rest : List Bool) (hin : C.cw.drop a.cp = d.word ++ rest) :
    Hs C truePaddingBody a (readScalarsCost d.fields + 520 * C.Wd + 5 * d.n + 1500)
      (fun b => b.out = a.out ++ d.padded ∧ b.cp = a.cp + d.word.length ∧
        b.wq = a.wq ∧ Cst b) := by
  refine Hx.hs (Hs.then (Hs.addValid (by omega) hv (parseInput_spec d hW hL a hc rest hin))
    (fun b ⟨⟨bs, bp, bw, bo, bc, _⟩, bv⟩ n1 hn1 => ?_))
  refine Hs.then (hs_emit C true b) (fun d0 hd0 n2 hn2 => ?_)
  subst hd0
  have cv : Valid C { b with out := b.out ++ [true] } := ⟨bv.env_lt, bv.cp_le, bv.wq_le⟩
  refine Hs.then (printVars_spec (C := C) inputVariables (by decide) hW3 _ ⟨bc.z, bc.one, bc.two, bc.pos⟩ cv)
    (fun c ⟨co, cp, cw, cc, cv', cf⟩ n3 hn3 => ?_)
  have cn : c.env inputN = d.n := by
    rw [cf inputN (by decide) (by decide)]
    exact bs.1
  have cword : inputVariables.flatMap (fun x => natWord (b.env x)) = d.word := d.stored_word bs
  refine Hs.last (appendPadding_spec c cc (cv'.env_lt inputN)) ?_
  rintro e ⟨eo, ep, ew, ec, _⟩ n4 hn4
  refine ⟨⟨?_, by rw [ep, cp, bp], by rw [ew, cw, bw], ec⟩, ?_⟩
  · rw [eo, cn, co]
    change (b.out ++ [true]) ++ inputVariables.flatMap (fun x => natWord (b.env x)) ++ _ = _
    rw [cword, bo]
    simp [Input.padded, List.append_assoc]
  · rw [cn] at hn4
    simp only [inputVariables, List.length_cons, List.length_nil, pvCost] at hn3
    omega

end NearQuarticWires.StageOutput
