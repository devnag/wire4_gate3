import Proof.Quartic.StageLiftTokens.Runtime
import Proof.Quartic.StageLiftTokens.InitialReady
import Proof.Quartic.StageLift.ResidueCacheContract

/-!
# Actual amplified residue-source program

`lem:residue`, `imp:amp` and `lem:print`, paper/paper.tex: the uniform physical source program reads
the original retained parameter, witness and normalized-index records,
emits the exact amplified formula, and preserves the compact-prefix
length as well as every fixed field of the source interface.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicGates.Close.Cells StageLift StageCert.Tokens

def residueBodyProgram : St VV MM := .seq initializeResidue amplifierProgram

theorem residueBodyProgram_run_withCache :
    residueBodyProgramWithCacheSpec residueBodyProgram := by
  intro B1 B2 C r a E h
  unfold residueBodyProgram
  apply Hx.hs
  refine Hs.then (initialize_ready C r a E h)
    (fun b ⟨bo,br,bmem,bcurs,bs,bfr⟩ n1 hn1=>?_)
  refine Hs.last (amplifierProgram_run C r b E br)
    (fun d ⟨doo,dr,df⟩ n2 hn2=>?_)
  refine ⟨⟨⟨?_,df.records.trans bmem,?_,df.streams.trans bs,dr.constants,dr.valid,?_⟩,?_⟩,?_⟩
  · rw [doo,bo]
  · intro store hs
    exact (df.cursors store hs).trans (bcurs store (by
      intro he
      subst store
      exact hs (by simp)))
  · intro x hx
    have hmem : x∈sourceRegisters := by
      simp only [sourceRegisters,List.mem_cons] at hx ⊢
      tauto
    have hnot : x∉[t2,vJ,c0,selectionStart,chainRows,newtonTau] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with h|h|h|h|h|h|h|h|h|h|h|h <;> subst x <;> decide
    exact (df.registers x hmem).trans (bfr x hnot)
  · exact (df.registers _ (by decide)).trans (bfr _ (by decide))
  · have hc:=actual_source_clock E _ _ h.chains_bound h.exponent_bound
    omega

theorem residueBodyProgram_run : residueBodyProgramSpec residueBodyProgram :=
  residueBodyProgramWithCacheSpec_weakens residueBodyProgram_run_withCache

end NearQuarticWires.StageLiftTokens
