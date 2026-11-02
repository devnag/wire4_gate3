import Proof.Quartic.StagePrint.PoolLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the concrete occurrence program uses a fixed number of tapes and registers for every original-bank size. -/
noncomputable def poolOccurrenceProgram (p : Program) : WMX (p.tapeCount+5) 16 :=
  poolOccurrence (poolSite p) (poolSource p) (poolOutput p) poolWriterRegs 12 13

/-- `lem:print`, paper/paper.tex: one original cache is physically computed in the concrete sequential pool layout. -/
theorem poolState_step {Request : Type} {input cache : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (req : Request)
    (cap : ℕ) (source : List Bool) (caches : ℕ→List Bool) (j left : ℕ)
    (hinput : input req=NearCubicWires.RepairRepresentation.natWord j++source)
    (hcache : cache req=caches j)
    (hwrite : j+8*natBitLength j+4*source.length+20≤cap)
    (hcall : 2*(input req).length+2+budget req≤cap)
    (hcopy : (poolPrefix caches j).length+(frame (caches j)).length+1≤cap) :
    ∃ τ, WXExec cap (poolOccurrenceProgram f.program) (poolState f.program source caches j left) τ
      (poolOccurrenceCost j source.length (input req).length (budget req)) ∧
      SimW (poolState f.program source caches (j+1) left) τ := by
  let σ:=poolState f.program source caches j left
  have hINB : ∀q,(poolSite f.program).bank q≠poolSource f.program := by
    intro q h
    have hv:=congrArg Fin.val h
    change 5+q.val=0 at hv
    omega
  have hpB : ∀q,(poolSite f.program).bank q≠poolOutput f.program := by
    intro q h
    have hv:=congrArg Fin.val h
    change 5+q.val=1 at hv
    omega
  have hST : poolOutput f.program≠(poolSite f.program).tally := by
    intro h;have hv:=congrArg Fin.val h;change 1=2 at hv;omega
  have hSG : poolOutput f.program≠(poolSite f.program).guard := by
    intro h;have hv:=congrArg Fin.val h;change 1=3 at hv;omega
  have hSL : poolOutput f.program≠(poolSite f.program).ruler := by
    intro h;have hv:=congrArg Fin.val h;change 1=4 at hv;omega
  have hCR : ∀i,(12 : Fin 16)≠poolWriterRegs i := by intro i;fin_cases i <;> decide
  have hS : ∀i,σ.val ((poolSite f.program).regs i)=0 := by
    intro i
    fin_cases i <;> rfl
  have hz : ∀i : Fin 8,i≠0→σ.val (poolWriterRegs i)=0 := by
    intro i hi
    fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  obtain ⟨τ,he,hpost⟩:=poolOccurrence_exec f req cap (poolSite f.program) (poolSource f.program)
    (poolOutput f.program) poolWriterRegs 12 13 hINB hpB hST hSG hSL hCR (by change (13 : Fin 16)≠poolSiteRegs 0;decide) (by decide)
    σ j source hinput
    (fun q=>(poolState_bank f.program source caches j left q).1)
    (fun q=>(poolState_bank f.program source caches j left q).2)
    rfl rfl rfl rfl (by rw [show σ.st (poolSite f.program).ruler=[] from rfl];exact Control.nil_blank)
    rfl hS rfl hz rfl rfl rfl rfl hwrite hcall
    (by change (poolPrefix caches j).length+(frame (cache req)).length+1≤cap;rw [hcache];exact hcopy)
  refine ⟨τ,he,?_⟩
  change SimW ((NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO
    (poolState f.program source caches j left) (poolOutput f.program) 13 (frame (cache req))).setv 4 (j+1)) τ at hpost
  rw [hcache,poolState_next] at hpost
  exact hpost

end NearQuarticWires.StagePrint
