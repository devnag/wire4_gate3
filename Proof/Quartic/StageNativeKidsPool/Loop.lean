import Proof.Quartic.StageNativeKidsPool.Layout

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control StageNativeKids StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
complete original-child family has one source and affine header; only
the computed child index changes between the real pipeline calls. -/
structure Family (Request : Type) (input : Request→List Bool) where
  count : ℕ
  source : List Bool
  header : List Bool
  request : Fin count→Request
  word_eq : ∀j,input (request j)=pipelineInputWord source (List.replicate j.val true) header

/-- `lem:print`, paper/paper.tex: unvisited
indices are empty and are never requested by the counted loop. -/
def Family.bytes {Request : Type} {input : Request→List Bool}
    (F : Family Request input) (records : Request→List (List Bool)) (j : ℕ) : List Bool :=
  if h:j<F.count then (records (F.request ⟨j,h⟩)).flatMap frame else []

/-- `lem:print`, paper/paper.tex: the
remaining ordered original field stream is defined by actual successive
indices and contains no separators between row outputs. -/
def suffix (bytes : ℕ→List Bool) (j : ℕ) : ℕ→List Bool
  | 0=>[]
  | left+1=>bytes j++suffix bytes (j+1) left

/-- `prop:time`, paper/paper.tex: the
finite sum of the actual row clocks bounds every visited row body. -/
def Family.stepBudget {Request : Type} {input : Request→List Bool}
    (F : Family Request input) (budget : Request→ℕ) : ℕ :=
  (List.ofFn fun j : Fin F.count=>occurrenceCost F.source F.header j.val
    (input (F.request j)).length (budget (F.request j))).sum

/-- `prop:time`, paper/paper.tex: each
actual original row's complete formatting and computation is charged. -/
theorem Family.step_le {Request : Type} {input : Request→List Bool}
    (F : Family Request input) (budget : Request→ℕ) (j : Fin F.count) :
    occurrenceCost F.source F.header j.val (input (F.request j)).length
      (budget (F.request j))≤F.stepBudget budget := by
  apply List.le_sum_of_mem
  exact List.mem_ofFn.mpr ⟨j,rfl⟩

/-- `lem:print`, paper/paper.tex: one
actual remaining-count loop executes its real row-call body in original
index order, including the zero-child case. -/
noncomputable def loopProgram {p : Program} (L : Layout p ns nr) : WMX ns nr :=
  .whr L.remaining (.seq (WMX.dec L.remaining)
    (occurrenceProgram L.site L.sources L.registers L.out L.outputCounter))

/-- `lem:print` and `prop:time`, paper/paper.tex: the full actual original-child loop retains
its exterior sources and prints all raw native rows in order, with
finite capacity and every real call and cleanup paid. -/
theorem loop_suffix {Request : Type} {input : Request→List Bool}
    {records : Request→List (List Bool)} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>(records r).flatMap frame) budget)
    (F : Family Request input) (L : Layout f.program ns nr) (cap : ℕ)
    (hne : ∀q,∀record∈records (F.request q),record≠[])
    (hcount : F.count≤cap)
    (hwrites : ∀j<F.count,4*((frame F.source).length+(frame F.header).length)+8*j+100≤cap)
    (hcalls : ∀q,2*(input (F.request q)).length+2+budget (F.request q)≤cap) :
    ∀left j (σ : WState ns nr),j+left=F.count→Ready L F.source F.header j left σ→
      σ.val L.outputCounter+(suffix (F.bytes records) j left).length+1≤cap→
      ∃ideal τ,Ready L F.source F.header F.count 0 ideal ∧
        WXExec cap (loopProgram L) σ τ (left*(F.stepBudget budget+10)+1) ∧
        SimW ideal τ ∧
        ideal.st L.out=σ.st L.out++suffix (F.bytes records) j left ∧
        ideal.val L.outputCounter=σ.val L.outputCounter+(suffix (F.bytes records) j left).length ∧
        (∀i,i≠L.out→ideal.st i=σ.st i ∧ ideal.sh i=σ.sh i) := by
  intro left
  induction left with
  | zero =>
    intro j σ hj hready _
    have he : j=F.count:=by omega
    subst he
    refine ⟨σ,σ,hready,?_,SimW.refl _,by simp [suffix],by simp [suffix],?_⟩
    · simpa only [loopProgram,zero_mul,zero_add] using
      (WXExec.whrF (cap:=cap) (r:=L.remaining)
        (P:=.seq (WMX.dec L.remaining)
          (occurrenceProgram L.site L.sources L.registers L.out L.outputCounter))
        (σ:=σ) hready.count)
    · intro i _;exact ⟨rfl,rfl⟩
  | succ left ih =>
    intro j σ hj hready hfit
    have hjlt : j<F.count:=by omega
    let q : Fin F.count:=⟨j,hjlt⟩
    let σd:=σ.setv L.remaining left
    have ed:=WXExec.dec cap L.remaining σ (by rw [hready.count];omega)
    rw [hready.count,Nat.add_sub_cancel] at ed
    change WXExec cap _ σ σd 1 at ed
    have hdready : Ready L F.source F.header j left σd:=hready.dec
    have hb : (records (F.request q)).flatMap frame=F.bytes records j := by
      simp only [Family.bytes,dif_pos hjlt,q]
    have hcopy : σd.val L.outputCounter+((records (F.request q)).flatMap frame).length+1≤cap := by
      simp only [suffix,List.length_append] at hfit
      simp only [σd,WState.setv_val,Function.update_of_ne L.remaining_output.symm]
      rw [hb]
      omega
    obtain ⟨τc,ec,hs⟩:=occurrence_exec f (F.request q) (hne q) cap L.site L.sources L.registers
      L.out L.outputCounter L.input_eq L.out_bank L.out_tally L.out_guard L.out_ruler
      L.counter_registers (L.counter_call 0) σd F.source F.header j (F.word_eq q)
      hdready.bank hdready.heads hdready.tally hdready.tally_head hdready.guard hdready.guard_head
      hdready.ruler hdready.ruler_head hdready.call_registers hdready.index hdready.scratch
      hdready.source hdready.header hdready.source_heads hdready.out_head (hwrites j hjlt)
      (hcalls q) hcopy
    let σnext:=(appendO σd L.out L.outputCounter ((records (F.request q)).flatMap frame)).setv
      (L.registers 0) (j+1)
    have hnready : Ready L F.source F.header (j+1) left σnext:=hdready.next _
    have hnfit : σnext.val L.outputCounter+(suffix (F.bytes records) (j+1) left).length+1≤cap := by
      simp only [suffix,List.length_append] at hfit
      simp only [σnext,appendO,WState.setv_val,Function.update_of_ne (L.counter_registers 0),
        Function.update_self,σd,Function.update_of_ne L.remaining_output.symm]
      rw [hb]
      omega
    obtain ⟨ideal,τend,hfinal,er,hr,hout,hop,hother⟩:=ih (j+1) σnext (by omega) hnready hnfit
    obtain ⟨τfinal,ea,ha⟩:=wxexec_sim er τc hs
    refine ⟨ideal,τfinal,hfinal,?_,SimW.trans hr ha,?_,?_,?_⟩
    · have ep:=WXExec.whrT (by rw [hready.count];omega) (WXExec.seq ed ec) ea
      refine ep.mono ?_
      have hc:=F.step_le budget q
      change occurrenceCost F.source F.header j (input (F.request q)).length
        (budget (F.request q))≤F.stepBudget budget at hc
      rw [Nat.succ_mul]
      omega
    · rw [hout]
      simp only [σnext,σd,appendO,WState.setv_st,WState.seth_st,WState.sets_st,
        Function.update_self,suffix,hb,List.append_assoc]
    · rw [hop]
      simp only [σnext,σd,appendO,WState.setv_val,Function.update_of_ne (L.counter_registers 0),
        Function.update_self,Function.update_of_ne L.remaining_output.symm,
        suffix,List.length_append,hb,Nat.add_assoc]
    · intro i hi
      obtain ⟨hst,hsh⟩:=hother i hi
      constructor
      · simpa [σnext,σd,appendO,Function.update_of_ne hi] using hst
      · simpa [σnext,σd,appendO,Function.update_of_ne hi] using hsh

end NearQuarticWires.StageNativeKidsPool
