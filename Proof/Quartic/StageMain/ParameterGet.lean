import Proof.Quartic.StageMain.CompactDecode
import Proof.Gates.Cells.Load2

/-!
# Reading a selected scalar from the actual parameter store

`sec:params`, paper/paper.tex, and Step 4 of
`sec:algorithm`: a fixed scalar position is read
by a paid store rewind and scan. The original certificate cursor,
the compact preparation word and the parameter records are preserved.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Cells
open StageLift

def readParameter (i : Fin 46) (dst : Fin VV) : St VV MM :=
  .seq (setK t2 i.val) (fetch parameterStore t2 dst)

def parameterRest (a : DS VV MM) :=
  (a.ip, a.out, a.ram, Function.update a.rc parameterStore 0, a.kin, a.kout, a.kc)

theorem readParameter_run (C : Ctx) (p : Cells.Parameters) (i : Fin 46) (dst : Fin VV)
    (a : DS VV MM) (hc : Cst a) (hstore : a.ram parameterStore = parameterScalars p)
    (hfit : i.val < 2 ^ C.Wd) (hdst : dst ∉ [vZ, v1, v2]) :
    Hs C (readParameter i dst) a (a.rc parameterStore + 7 * i.val + 13) (fun b =>
      b.env dst = (parameterScalars p).getD i.val 0 ∧
      b.rc parameterStore = i.val + 1 ∧ parameterRest b = parameterRest a ∧
      Cst b ∧ Fr a b [t2, vJ, c0, dst]) := by
  unfold readParameter
  refine (Hs.seq (t2 := a.rc parameterStore + 5 * i.val + 9)
    (setK_spec t2 (by decide) i.val a hfit) ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbi, hbsh, hbfr⟩
  have hsame := Same.of_sh hbsh
  have hfetch := fetch_spec (C := C) parameterStore t2 dst (by decide) (by decide) b
    (by rw [hbi, hsame.ram, hstore, parameterScalars_length]; exact i.isLt)
    (by rw [hbi]; exact hfit)
  rw [hsame.rc, hbi] at hfetch
  refine hfetch.mono le_rfl ?_
  rintro d ⟨hdv, hdip, hdo, hdram, hdrc, hdkin, hdkout, hdkc, hdfr⟩
  have hframes : Fr a d [t2, vJ, c0, dst] :=
    (hbfr.weaken (by simp)).trans (hdfr.weaken (by simp))
  refine ⟨?_, ?_, ?_, Cst.of_fr hc hframes ?_, hframes⟩
  · rw [hdv, hsame.ram, hstore]
  · rw [hdrc, Function.update_self]
  · simp only [parameterRest, hdip, hdo, hdram, hdrc, hdkin, hdkout, hdkc,
      hsame.ip, hsame.out, hsame.ram, hsame.kin, hsame.kout, hsame.kc,
      Function.update_idem]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdst ⊢
    exact ⟨⟨by decide, by decide, by decide, Ne.symm hdst.1⟩,
      ⟨by decide, by decide, by decide, Ne.symm hdst.2.1⟩,
      by decide, by decide, by decide, Ne.symm hdst.2.2⟩

end NearQuarticWires.StageMain
